/* IGC 解析 + 飞行分析核心（与 analyze_igc.py 同口径的 JS 移植）
 *  - 地速: 10 秒位移平滑 (GPS, 对地含风)
 *  - 爬升率: 气压高度 10 秒线性回归斜率
 *  - 滑翔比: 30 秒直线窗口 (航向变化<=60°) 水平距离/掉高, 仅净下降>=15m
 *  - 盘升: 转弯率>5°/s 持续 且 累计航向>=270°
 * 既可在浏览器里用 (window.IGCCore), 也可在 Node 里跑测试 (module.exports) */
(function (root) {
  'use strict';
  var R = 6371000, DEG = Math.PI / 180;

  function hav(lat1, lon1, lat2, lon2) {
    var p1 = lat1 * DEG, p2 = lat2 * DEG;
    var dp = (lat2 - lat1) * DEG, dl = (lon2 - lon1) * DEG;
    var a = Math.sin(dp / 2) * Math.sin(dp / 2) +
      Math.cos(p1) * Math.cos(p2) * Math.sin(dl / 2) * Math.sin(dl / 2);
    return 2 * R * Math.asin(Math.sqrt(a));
  }

  var CIRCLE_RATE = 5.0, MIN_THERMAL_S = 20, MIN_NET_DEG = 270;
  var GLIDE_HALF = 15, GLIDE_MIN_SINK = 15.0, GLIDE_MAX_HDG = 60.0, LD_CAP = 20.0;

  /* ---------------- 解析 ---------------- */
  function parseIGC(text) {
    var lines = text.split(/\r\n|\r|\n/);
    var date = null, glider = '', rollover = 0, last = -1;
    var T = [], LA = [], LO = [], PA = [], GA = [];
    for (var li = 0; li < lines.length; li++) {
      var line = lines[li].trim();
      if (date === null && (line.indexOf('HFDTE') === 0)) {
        var m = line.match(/(\d{2})(\d{2})(\d{2})/);
        if (m) {
          var d = new Date(Date.UTC(2000 + +m[3], +m[2] - 1, +m[1]));
          if (!isNaN(d.getTime())) date = d;
        }
      }
      if (!glider && line.indexOf('HFGTYGLIDERTYPE:') === 0) glider = line.slice(16).trim();
      if (line.charAt(0) !== 'B' || line.length < 35) continue;
      var hh = +line.substr(1, 2), mm = +line.substr(3, 2), ss = +line.substr(5, 2);
      var la = +line.substr(7, 2) + (+line.substr(9, 2) + +line.substr(11, 3) / 1000) / 60;
      var lo = +line.substr(15, 3) + (+line.substr(18, 2) + +line.substr(20, 3) / 1000) / 60;
      var pa = +line.substr(25, 5), ga = +line.substr(30, 5);
      if ([hh, mm, ss, la, lo, pa, ga].some(isNaN)) continue;
      if (line.charAt(14) === 'S') la = -la;
      if (line.charAt(23) === 'W') lo = -lo;
      if (line.charAt(24) !== 'A') continue;
      var t = hh * 3600 + mm * 60 + ss + rollover;
      if (t < last - 43200) { rollover += 86400; t += 86400; }
      last = t;
      T.push(t); LA.push(la); LO.push(lo); PA.push(pa); GA.push(ga);
    }
    return {
      t: Float64Array.from(T), lat: Float64Array.from(LA), lon: Float64Array.from(LO),
      palt: Float64Array.from(PA), galt: Float64Array.from(GA), date: date, glider: glider
    };
  }

  /* ---------------- 派生量 ---------------- */
  /* 气压高度 10s 回归斜率, 窗口 [i-5, i+4] (与 numpy convolve 'same' 对齐) */
  function rollingSlope10(y) {
    var n = y.length, out = new Float64Array(n).fill(NaN), w = 10, h = 5;
    var sx = 0, sx2 = 0, m, i, k;
    for (m = 0; m < w; m++) { sx += m; sx2 += m * m; }
    var xb = sx / w, den = sx2 - w * xb * xb;
    for (i = h; i <= n - 1 - (w - h); i++) {
      var sxy = 0, sy = 0;
      for (k = 0; k < w; k++) { var v = y[i - h + k]; sy += v; sxy += k * v; }
      out[i] = (sxy - sy * xb) / den;
    }
    return out;
  }

  function analyze(flt) {
    var t = flt.t, lat = flt.lat, lon = flt.lon, palt = flt.palt;
    var n = t.length;
    if (n < 200) throw new Error('有效 B 记录太少 (' + n + ')');

    /* 气压高度无效(恒0/恒定)时回退 GPS 高度 */
    var altSrc = '气压', i, k;
    (function () {
      var mn = Infinity, mx = -Infinity, gm = Infinity, gx = -Infinity, g = flt.galt;
      for (i = 0; i < n; i++) {
        if (palt[i] < mn) mn = palt[i];
        if (palt[i] > mx) mx = palt[i];
        if (g[i] < gm) gm = g[i];
        if (g[i] > gx) gx = g[i];
      }
      if (mx - mn < 1 && gx - gm > 10) { palt = Float64Array.from(g); altSrc = 'GPS'; }
    })();

    var lat0 = 0, lon0 = 0, i, k;
    for (i = 0; i < n; i++) { lat0 += lat[i]; lon0 += lon[i]; }
    lat0 /= n; lon0 /= n;
    var cosl = Math.cos(lat0 * DEG);
    var X = new Float64Array(n), Y = new Float64Array(n);
    for (i = 0; i < n; i++) {
      X[i] = R * (lon[i] - lon0) * DEG * cosl;
      Y[i] = R * (lat[i] - lat0) * DEG;
    }

    /* 地速: ±5 样本位移 */
    var v10 = new Float64Array(n);
    for (i = 0; i < n; i++) {
      var a = Math.max(0, i - 5), b = Math.min(n - 1, i + 5);
      v10[i] = hav(lat[a], lon[a], lat[b], lon[b]) / Math.max(t[b] - t[a], 1e-6);
    }

    /* 航向 / 转弯率(5s) */
    var hdg = new Float64Array(n);
    for (i = 0; i < n - 1; i++) {
      hdg[i + 1] = Math.atan2(X[i + 1] - X[i], Y[i + 1] - Y[i]);
    }
    hdg[0] = hdg[1];
    var hun = new Float64Array(n);
    hun[0] = hdg[0];
    for (i = 1; i < n; i++) {           /* unwrap */
      var d = hdg[i] - hdg[i - 1];
      d = ((d + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI;
      hun[i] = hun[i - 1] + d;
    }
    var turn = new Float64Array(n);
    for (i = 2; i < n - 2; i++) turn[i] = (hun[i + 2] - hun[i - 2]) / DEG / 4;

    var vario = rollingSlope10(palt);

    /* 在空中: v10>2 且 20s 窗口 [i-10,i+9] 内至少 18 秒 (整数计数, 与 Python 同规则) */
    var raw = new Uint8Array(n), inflight = new Uint8Array(n), any = 0;
    for (i = 0; i < n; i++) { raw[i] = v10[i] > 2 ? 1 : 0; if (raw[i]) any = 1; }
    if (any) {
      for (i = 0; i < n; i++) {
        var c = 0, j, lo = Math.max(0, i - 10), hi = Math.min(n - 1, i + 9);
        for (j = lo; j <= hi; j++) c += raw[j];
        inflight[i] = c >= 18 ? 1 : 0;
      }
    } else {
      inflight.set(raw);
    }

    /* 盘升检测 */
    var thermals = detectThermals(t, X, Y, palt, hun, turn, v10, vario, inflight);
    var circling = new Uint8Array(n);
    thermals.forEach(function (th) {
      for (i = th.i0; i <= th.i1; i++) circling[i] = 1;
    });

    /* 滑翔比窗口 */
    var gw = glideWindows(t, lat, lon, palt, hun, inflight, circling);

    /* 最佳爬升 */
    function bestClimb(w) {
      var best = -1e18, bk = -1;
      for (i = 0; i + w < n; i++) {
        if (!inflight[i + w] || !inflight[i]) continue;
        var g = palt[i + w] - palt[i];
        if (g > best) { best = g; bk = i; }
      }
      return { v: best >= -1e17 ? best / w : NaN, k: bk };
    }
    var b30 = bestClimb(30), b60 = bestClimb(60), b300 = bestClimb(300);

    /* 总量 */
    var distTotal = 0, totalClimb = 0;
    for (i = 0; i < n - 1; i++) {
      if (inflight[i] && inflight[i + 1]) {
        distTotal += hav(lat[i], lon[i], lat[i + 1], lon[i + 1]);
        var dp = palt[i + 1] - palt[i];
        if (dp > 0) totalClimb += dp;
      }
    }
    var dur = t[n - 1] - t[0], climbT = 0, glideT = 0;
    for (i = 0; i < n; i++) {
      if (!inflight[i] || isNaN(vario[i])) continue;
      if (vario[i] > 0.2) climbT++;
      else if (vario[i] < -0.2 && !circling[i]) glideT++;
    }
    var vMax = 0, altMax = -1e9, altMin = 1e9, segs = 1;
    for (i = 0; i < n; i++) {
      if (inflight[i] && v10[i] > vMax) vMax = v10[i];
      if (palt[i] > altMax) altMax = palt[i];
      if (palt[i] < altMin) altMin = palt[i];
      if (i && t[i] - t[i - 1] > 180) segs++;
    }

    return {
      t: t, lat: lat, lon: lon, x: X, y: Y, palt: palt, galt: flt.galt,
      glider: flt.glider, altSrc: altSrc,
      v10: v10, vario: vario, turn: turn, inflight: inflight, circling: circling,
      thermals: thermals, glideWindows: gw,
      b30: b30.v, k30: b30.k, b60: b60.v, k60: b60.k, b300: b300.v, k300: b300.k,
      distTotal: distTotal, straight: hav(lat[0], lon[0], lat[n - 1], lon[n - 1]),
      totalClimb: totalClimb, dur: dur, climbT: climbT, glideT: glideT,
      vMax: vMax, altMax: altMax, altMin: altMin, date: flt.date, nSegments: segs
    };
  }

  function detectThermals(t, X, Y, palt, hun, turn, v10, vario, inflight) {
    var n = t.length, idx = [], i;
    for (i = 0; i < n; i++) if (inflight[i] && Math.abs(turn[i]) > CIRCLE_RATE) idx.push(i);
    if (!idx.length) return [];
    var groups = [[idx[0]]];
    for (i = 1; i < idx.length; i++) {
      if (idx[i] - idx[i - 1] > 6) groups.push([idx[i]]);
      else groups[groups.length - 1].push(idx[i]);
    }
    var out = [];
    groups.forEach(function (g) {
      var i0 = g[0], i1 = g[g.length - 1];
      if (t[i1] - t[i0] < MIN_THERMAL_S) return;
      var net = (hun[i1] - hun[i0]) / DEG;
      if (Math.abs(net) < MIN_NET_DEG) return;
      var dur = t[i1] - t[i0], gain = palt[i1] - palt[i0], vbest = NaN;
      for (var j = i0; j <= i1; j++) {
        var v = vario[j];
        if (!isNaN(v) && (isNaN(vbest) || v > vbest)) vbest = v;
      }
      var spd = 0; for (j = i0; j <= i1; j++) spd += v10[j]; spd /= (i1 - i0 + 1);
      var omega = Math.abs(net) * DEG / dur;
      var wx = (X[i1] - X[i0]) / dur, wy = (Y[i1] - Y[i0]) / dur;
      out.push({
        i0: i0, i1: i1, t0: t[i0], dur: dur, gain: gain, climb: gain / dur,
        vbest: vbest, right: net > 0, turns: Math.abs(net) / 360,
        radius: omega > 0 ? spd / omega : NaN, spd: spd,
        wind: Math.hypot(wx, wy),
        windFrom: (Math.atan2(-wx, -wy) / DEG + 360) % 360
      });
    });
    return out;
  }

  function glideWindows(t, lat, lon, palt, hun, inflight, circling) {
    var n = t.length, rows = [], h = GLIDE_HALF;
    for (var k = h; k < n - h; k++) {
      if (!inflight[k - h] || !inflight[k + h] || circling[k - h] || circling[k + h]) continue;
      var dalt = palt[k + h] - palt[k - h];
      if (dalt > -GLIDE_MIN_SINK) continue;
      var net = (hun[k + h] - hun[k - h]) / DEG;
      if (Math.abs(net) > GLIDE_MAX_HDG) continue;
      var dh = hav(lat[k - h], lon[k - h], lat[k + h], lon[k + h]);
      var ld = dh / -dalt;
      if (ld <= 0 || ld > LD_CAP) continue;
      rows.push({ t: t[k], spd: dh / (2 * h), sink: -dalt / (2 * h), ld: ld });
    }
    return rows;
  }

  /* ---------------- 汇总数字 ---------------- */
  function median(a) {
    if (!a.length) return NaN;
    var b = a.slice().sort(function (x, y) { return x - y; });
    var m = b.length >> 1;
    return b.length % 2 ? b[m] : (b[m - 1] + b[m]) / 2;
  }
  function percentile(a, p) {
    if (!a.length) return NaN;
    var b = a.slice().sort(function (x, y) { return x - y; });
    var pos = (b.length - 1) * p, lo = Math.floor(pos), hi = Math.ceil(pos);
    return b[lo] + (b[hi] - b[lo]) * (pos - lo);
  }

  function summary(res) {
    var lds = res.glideWindows.map(function (g) { return g.ld; });
    var spds = res.glideWindows.map(function (g) { return g.spd * 3.6; });
    var cl = res.thermals.map(function (th) { return th.climb; });
    var circ = 0; res.thermals.forEach(function (th) { circ += th.dur; });
    return {
      dur: res.dur, dist: res.distTotal, altMax: res.altMax, altMin: res.altMin,
      totalClimb: res.totalClimb, vMaxKmh: res.vMax * 3.6,
      ldMed: median(lds), ldP90: percentile(lds, 0.9), cruiseKmh: median(spds),
      b30: res.b30, b60: res.b60, b300: res.b300,
      nThermals: res.thermals.length,
      meanClimb: cl.length ? cl.reduce(function (a, b) { return a + b; }, 0) / cl.length : NaN,
      circPct: 100 * circ / Math.max(res.dur, 1), nSegments: res.nSegments
    };
  }

  /* 滑翔比-速度分档 (2 km/h) */
  function ldBySpeedBin(res) {
    var bins = {};
    res.glideWindows.forEach(function (g) {
      var lo = Math.floor(g.spd * 3.6 / 2) * 2;
      var key = lo + '-' + (lo + 2);
      (bins[key] = bins[key] || []).push(g.ld);
    });
    return Object.keys(bins).sort(function (a, b) { return +a.split('-')[0] - +b.split('-')[0]; })
      .map(function (key) {
        return { bin: key, n: bins[key].length, ld: median(bins[key]) };
      });
  }

  var api = { parseIGC: parseIGC, analyze: analyze, summary: summary, ldBySpeedBin: ldBySpeedBin };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.IGCCore = api;
})(this);
