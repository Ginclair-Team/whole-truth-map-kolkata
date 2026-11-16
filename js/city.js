/* Pixel Kolkata - the procedural city. Everything static is drawn here through the PK.E rasteriser.
   build() runs two identical deterministic passes: a dry pass (ground paint + cast shadows),
   E.renderGround(), then the real pass (all pixels). */
(function (root) {
  'use strict';
  const PK = (root.PK = root.PK || {});
  const E = PK.E, L = PK.L;
  if (!E || !L) throw new Error('city.js needs engine.js and layout.js loaded first');
  const T = E.T, C = E.C, sh = E.sh, GW = E.GW, GH = E.GH, OCC = E.OCC, RD = E.RD, hs = E.hs, sx = E.sx, sy = E.sy;
  const { box, wallM, roofM, stripeM, crowdM, drum, dome, spire, stack, pyr, gable, line3, pt, stamp, person, crowd, tree, vehicle, light, gRect, gFn, gDisc, claim, isFree, road } = E;

  /* ---------- tiny helpers ---------- */
  const ri = (r, n) => (r() * n) | 0;
  const pick = (r, a) => a[(r() * a.length) | 0];
  const lerp = L.lerp;
  const R = (x, y, w, h, c, d) => { if (!E.S.dry) E.rect(x, y, w, h, c, d); };   // rect is not dry-guarded in the engine
  const LN = (x0, y0, x1, y1, c, d) => { if (!E.S.dry) E.line(x0, y0, x1, y1, c, d); };
  const PCOL = ['#d8452f', '#2f66b0', '#e8c032', '#4d9a6a', '#e9e2d0', '#8a3f8f', '#f08a24', '#f1c6a8', '#c43a8a'].map(C);
  const AW = [['#d8453a', '#f1ead8'], ['#2f8f5a', '#f1ead8'], ['#e8892a', '#f6d255'], ['#2f6fb5', '#f1ead8'], ['#c43a8a', '#f6d255'], ['#e5b82e', '#d8453a'], ['#7a3a9a', '#f6d255'], ['#18a0a0', '#f1ead8']].map((p) => p.map(C));
  const TARP = ['#3b78c2', '#e8892a', '#c9a55a', '#d8453a', '#2f8f5a', '#e8c032', '#c43a8a', '#18a0a0'].map(C);
  const ROOFS = ['#b8ac98', '#a79a86', '#c4b8a4', '#9d9283', '#b9654d', '#8d8478'].map(C);
  const SAREE = ['#d8453a', '#2f6fb5', '#e8c032', '#2f8f5a', '#c43a8a', '#f08a24', '#7a3a9a', '#18a0a0'].map(C);
  const BOOK = ['#d8453a', '#2f6fb5', '#e8c032', '#2f8f5a', '#f1ead8', '#7a3a9a', '#f08a24'].map(C);
  const WH = C('#f4f0e4'), GOLD = C('#e8b830'), STEEL = C('#9aa5ad'), STEELD = C('#7d8891'), BLK = C('#2a2a30'), WOOD = C('#9a7a52'), CREAM = C('#f1e6c8');
  const BRICK = C('#b4503a');

  const shadeM = (m, f) => (a, t, h, x, y, d) => sh(m(a, t, h, x, y, d), f);
  const pairM = (mk, f) => [mk(), shadeM(mk(), f || 0.72)];
  const wl = (base, o) => pairM(() => wallM(base, o));
  function colM(base, o) {   // arcade / colonnade ground floor, windowed floors above
    o = o || {};
    const ch = o.ch || 8, per = o.per || 4, dk = o.dark || sh(base, 0.42), cap = o.cap || sh(base, 0.9), colc = o.colc || base;
    const up = wallM(base, { cw: o.cw || 4, ww: 2, wh: 3, b0: ch, win: o.win || sh(base, 0.5), litP: o.litP == null ? 0 : o.litP, band: o.band, cornice: o.cornice, rh: o.rh || 6, wy: o.wy == null ? 2 : o.wy });
    return (a, t, h, x, y, d) => {
      const fb = h - 1 - t;
      if (fb < ch) { if (fb === 0) return cap; if (fb === ch - 1) return colc; const m = a % per; return m === 0 ? colc : m === 1 ? sh(colc, 0.85) : dk; }
      return up(a, t, h, x, y, d);
    };
  }
  function patM(c1, c2, c3) {
    return (a, t, h) => {
      const fb = h - 1 - t, u = (a + fb) % 8, v = (a - fb + 800) % 8;
      if (fb > h - 3 || fb < 2 || u < 1 || v < 1) return c2;
      return ((a >> 3) & 1) === 0 ? c1 : c3;
    };
  }
  const openF = (base) => (a, t) => (t === 0 || a % 7 === 0 ? base : C('#2a211c'));

  function ground(i, j, w, d, t) { gRect(i, j, w, d, t); claim(i, j, w, d); }
  function claimFn(i0, j0, i1, j1, fn) {
    for (let b = Math.max(0, Math.floor(j0)); b < Math.min(GH, Math.ceil(j1)); b++)
      for (let a = Math.max(0, Math.floor(i0)); a < Math.min(GW, Math.ceil(i1)); a++) if (fn(a + 0.5, b + 0.5)) OCC[b * GW + a] = 1;
  }
  function groundFn(i0, j0, i1, j1, fn) { gFn(i0, j0, i1, j1, fn); claimFn(i0, j0, i1, j1, (i, j) => fn(i, j)); }
  function groundDisc(ci, cj, ri_, rj, t) { gDisc(ci, cj, ri_, rj, t); claimFn(ci - ri_, cj - rj, ci + ri_, cj + rj, (i, j) => ((i - ci) / ri_) ** 2 + ((j - cj) / rj) ** 2 <= 1.15); }

  function B(i, j, w, d, h, base, o) {
    o = o || {};
    const z = o.z || 0, ins = o.ins || 0, m = o.mats || wl(base, o);
    if (!o.nc) claim(i, j, w, d);
    const roof = o.roof === undefined ? roofM(sh(base, 0.88)) : o.roof;
    box(i + ins, j + ins, w - 2 * ins, d - 2 * ins, h, z, roof, m[0], m[1], o.bo);
    return z + h;
  }
  function glow(i, j, z, c) { pt(i, j, z, c, 0.1); light(Math.round(sx(i, j)), Math.round(sy(i, j, z)), c, i + j + 0.1); }
  function bulbs(a, b, sag, cols, per) {
    const len = Math.hypot(b[0] - a[0], b[1] - a[1]), n = Math.max(2, Math.ceil(len * (per || 2.5)));
    for (let k = 0; k <= n; k++) {
      const t = k / n;
      glow(a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t - sag * Math.sin(Math.PI * t), cols[k % cols.length]);
    }
  }
  function pole(i, j, h, c) { line3([i, j, 0], [i, j, h], c || C('#5a4a3a'), 0.12); }
  function lamp(i, j) { pole(i, j, 11, C('#3a3a44')); glow(i, j, 12, C('#ffe08a')); }
  function clock(i, j, z) {
    const x = Math.round(sx(i, j)), y = Math.round(sy(i, j, z)), d = i + j + 1.0, k = C('#2a2430'), c = C('#f6f0dc');
    for (let dy = -3; dy <= 3; dy++) for (let dx = -3; dx <= 3; dx++) { const q = dx * dx + dy * dy; if (q <= 10) R(x + dx, y + dy, 1, 1, q > 5 ? k : c, d); }
    R(x, y - 2, 1, 3, k, d + 0.01); R(x, y, 2, 1, k, d + 0.01);
  }
  function mound(i, j, cols) {
    const x = Math.round(sx(i, j)), y = Math.round(sy(i, j)), d = i + j + 0.15;
    const rows = [[-2, 2, -1], [-1, 1, -2], [0, 0, -3]];
    for (const [a, b, dy] of rows) for (let dx = a; dx <= b; dx++) R(x + dx, y + dy, 1, 1, cols[hs(x + dx, y + dy) % cols.length], d);
  }
  function ring(ci, cj, rad, c, n) { for (let k = 0; k < n; k++) { const a = (k / n) * Math.PI * 2; pt(ci + Math.cos(a) * rad, cj + Math.sin(a) * rad, 0, c, 0.3); } }
  function chimney(i, j, h, c) { stack(i, j, 0.9, 0.9, h, 0, (t) => 0.07 * t, sh(c, 1.1), c, sh(c, 0.72)); stack(i + 0.04, j + 0.04, 0.82, 0.82, 2, h - 6, () => 0, BLK, sh(c, 0.5), sh(c, 0.4)); }
  function minaret(i, j, h, wallc, capc) {
    B(i, j, 0.9, 0.9, h, wallc, { cw: 4, ww: 1, wh: 3, win: sh(wallc, 0.55), litP: 0, band: CREAM, roof: sh(wallc, 1.05) });
    box(i - 0.18, j - 0.18, 1.26, 1.26, 2, h * 0.72, CREAM, sh(CREAM, 0.95), sh(CREAM, 0.72), { ns: 1 });
    box(i + 0.1, j + 0.1, 0.7, 0.7, 5, h, sh(wallc, 1.05), wallc, sh(wallc, 0.74), { ns: 1 });
    dome(i + 0.45, j + 0.45, h + 5, 0.5, 6, capc);
  }
  function churchSpire(i, j, w, d, h, sp, base, tilec) { // tower + spire
    B(i, j, w, d, h, base, { cw: 4, ww: 1, wh: 3, litP: 0, band: sh(base, 0.85) });
    spire(i + w / 2, j + d / 2, h, w * 0.62, sp, tilec);
  }
  function palmRow(i0, j0, i1, j1, n, r) { for (let k = 0; k < n; k++) { const i = (i0 + r() * (i1 - i0)) | 0, j = (j0 + r() * (j1 - j0)) | 0; if (isFree(i, j, 1, 1)) { tree(i, j, 2, i * 5 + j); claim(i, j, 1, 1); } } }

  /* ---------- trees, courtyards, maidan ---------- */
  function treeKind(r) { const u = r(); return u < 0.22 ? 3 : u < 0.42 ? 6 : u < 0.56 ? 0 : u < 0.66 ? 7 : u < 0.78 ? 1 : u < 0.88 ? 5 : u < 0.94 ? 4 : 2; }
  function treeCell(i, j, r, court) {
    if (court) gRect(i, j, 1, 1, T.PLAZA);
    tree(i, j, treeKind(r), i * 31 + j * 17);
    if (court) { const n = 1 + ri(r, 3); for (let k = 0; k < n; k++) person(i + 0.15 + r() * 0.7, j + 0.5 + r() * 0.45, pick(r, PCOL)); }
    claim(i, j, 1, 1);
  }
  function maidan(i0, j0, i1, j1, r, o) {
    o = o || {};
    const tp = o.tp || 0.07;
    for (let j = j0; j < j1; j++) for (let i = i0; i < i1; i++) {
      if (!isFree(i, j, 1, 1)) continue;
      const u = r();
      if (u < tp) { const k = r(); tree(i, j, k < 0.3 ? 0 : k < 0.5 ? 7 : k < 0.65 ? 1 : k < 0.8 ? 3 : k < 0.9 ? 6 : 5, i * 13 + j * 7); claim(i, j, 1, 1); }
      else if (u < tp + 0.03) { for (let k = 0, n = 1 + ri(r, 3); k < n; k++) person(i + r(), j + r(), pick(r, PCOL)); }
      else if (u < tp + 0.036 && isFree(i, j, 2, 2)) {
        ground(i, j, 2, 2, T.DIRT);
        for (let k = 0; k < 5; k++) person(i + 0.1 + r() * 1.8, j + 0.1 + r() * 1.8, k < 3 ? C('#f1ead8') : pick(r, PCOL));
        pt(i + 1, j + 1, 1, C('#f1ead8'), 0.2); pt(i + 1, j + 1, 2, C('#f1ead8'), 0.2);
      }
    }
  }

  /* ---------- stalls ---------- */
  function smallStall(i, j, r) {
    const c = pick(r, TARP), g = pick(r, TARP), alt = r() < 0.5;
    claim(i, j, 1, 1);
    box(i + 0.12, j + 0.15, 0.76, 0.7, 3, 0, stripeM(c, C('#f1ead8'), alt, 3),
      (a, t) => (t === 0 ? c : hs(a >> 1, i * 5 + j) % 3 === 0 ? C('#3a2a22') : g), (a, t) => sh(t === 0 ? c : g, 0.74), { ns: 1 });
  }
  function stalls(i0, j0, i1, j1, r, o) {
    o = o || {};
    const rs = o.rs || 2, p = o.p == null ? 0.7 : o.p;
    for (let cj = j0; cj < j1; cj += rs) {
      for (let ci = i0; ci < i1; ci++) {
        if (!isFree(ci, cj, 1, 1)) continue;
        if (r() < p) { smallStall(ci, cj, r); person(ci + 0.3 + r() * 0.4, cj + 1.05, pick(r, PCOL)); }
      }
      if (rs > 1) for (let ci = i0; ci < i1; ci++) {
        if (!isFree(ci, cj + 1, 1, 1)) continue;
        gRect(ci, cj + 1, 1, 1, T.LANE); claim(ci, cj + 1, 1, 1);
        if (r() < 0.45) person(ci + 0.2 + r() * 0.6, cj + 1 + r() * 0.8, pick(r, PCOL));
      }
    }
  }

  /* ---------- the generic filler ---------- */
  const STY = {
    north: { cols: ['#e6cf8e', '#d9a03f', '#e3a59a', '#b8cfa0', '#f1e6c8', '#a9c7d6', '#c96f5a'], shut: ['#2f6b4f', '#2f7f7a'], fl: [2, 3], plinth: '#a33b2e', mw: 2, md: 2, shopP: 0.2 },
    burra: { cols: ['#e6cf8e', '#d9a03f', '#e3a59a', '#b8cfa0', '#f1e6c8', '#a9c7d6', '#c96f5a'], shut: ['#2f6b4f', '#2f7f7a'], fl: [3, 5], plinth: '#a33b2e', mw: 2, md: 2, shopP: 0.55 },
    office: { cols: ['#f1e6c8', '#b4503a', '#e8c468', '#d8d0c0'], shut: ['#3d5a6b', '#4a4a56'], fl: [3, 4], mw: 3, md: 3, shopP: 0.08, cornice: 1, band: 1 },
    park: { cols: ['#f3ead6', '#e8d9b5', '#d9c3a0', '#c9d6cf', '#e6b8a8'], shut: ['#3d6e7a', '#2f5f4a', '#a8453a'], fl: [3, 4], mw: 2, md: 2, shopP: 0.4, band: 1, cornice: 1 },
    south: { cols: ['#f2efe6', '#e9d8c4', '#cfe0d6', '#e6c9c9', '#d8d2e6'], shut: ['#4a7a9a', '#3f7f6a', '#c0654a'], fl: [3, 4], mw: 2, md: 2, shopP: 0.15, band: 1 },
    garia: { cols: ['#f2efe6', '#f6d48a', '#e8a8a0', '#cfe0d6', '#d8d2e6', '#e9d8c4'], shut: ['#4a7a9a', '#3f7f6a', '#c0654a'], fl: [3, 4], mw: 2, md: 2, shopP: 0.7, band: 1, saree: 1, kite: 0.06 },
    howrah: { cols: ['#b4503a', '#8f9aa0', '#b4503a', '#a8452f'], fl: [1, 2], mw: 3, md: 2, shopP: 0, shed: 1, chim: 2, cw: 7 },
    modern: { cols: ['#6fa8c9', '#4f8fb0', '#8fc2c9', '#b9c7d0'], fl: [8, 12], mw: 3, md: 3, minw: 2, shopP: 0, cw: 3, glass: 1 },
  };

  function clutter(i, j, w, d, h, r, base) {
    if (r() < 0.5) { const sw = Math.min(0.45, w), sd = Math.min(0.45, d); B(i + r() * (w - sw), j + r() * (d - sd), sw, sd, 4, sh(base, 0.8), { z: h, nc: 1, mats: [sh(base, 0.95), sh(base, 0.7)], roof: sh(base, 0.8) }); }
    if (r() < 0.25) { const tw = Math.min(0.16, w, d); box(i + r() * (w - tw), j + r() * (d - tw), tw, tw, 2, h, BLK, BLK, BLK, { ns: 1 }); }
    if (r() < 0.35) { const lj = j + r() * Math.max(0.01, d - 0.1), li = i + r() * Math.max(0, w - 0.5), k0 = ri(r, PCOL.length); for (let k = 0; k < 4; k++) pt(li + k * 0.125, lj, h + 1, PCOL[(k0 + k) % PCOL.length], 0.15); }
    if (r() < 0.3) { pt(i + r() * w, j + r() * d, h + 1, C('#3f8a3f'), 0.15); pt(i + r() * w, j + r() * d, h + 1, C('#5aa84a'), 0.15); }
  }
  function building(i, j, w, d, s, r, o) {
    o = o || {};
    const base = C(pick(r, s.cols)), fl = Math.min(o.cap || 99, s.fl[0] + ri(r, s.fl[1] - s.fl[0] + 1));
    const shop = r() < (o.shopP != null ? o.shopP : s.shopP), aw = pick(r, AW), seed = (i * 7 + j * 13) & 255;
    const h = s.shed ? 7 + ri(r, 6) : fl * 6 + 2 + (shop ? 5 : 0);
    const winc = s.shut ? C(pick(r, s.shut)) : s.glass ? sh(base, 0.5) : s.shed ? BLK : undefined;
    const cw = s.cw || (r() < 0.3 ? 5 : 4);
    const wo = { cw, win: winc, seed, plinth: s.plinth ? C(s.plinth) : undefined, cornice: s.cornice ? sh(base, 1.12) : undefined, band: s.band ? sh(base, 0.84) : undefined, shop: shop ? [aw[0], aw[1], C('#2a2224')] : undefined, litP: s.glass ? 2 : 3 };
    if (s.glass) { wo.wy = 1; wo.wh = 4; wo.ww = 2; }
    if (s.shed) { wo.wy = 3; wo.wh = 2; wo.ww = 3; wo.litP = 6; }
    const saree = s.saree && shop;
    const mk = () => {
      const m = wallM(base, wo);
      if (!saree) return m;
      return (a, t, hh, x, y, dd) => { const fb = hh - 1 - t; if (fb >= 5 && fb < 11 && a % 3 === 0) return SAREE[((a / 3) | 0) + seed & 7]; return m(a, t, hh, x, y, dd); };
    };
    const m = pairM(mk), rc = pick(r, ROOFS), ins = 0.125;
    claim(i, j, w, d);
    const bi = i + ins, bj = j + ins, ww = w - 2 * ins, dd = d - 2 * ins;
    box(bi, bj, ww, dd, h, 0, roofM(rc), m[0], m[1]);
    if (s.shed) gable(bi, bj, ww, dd, 4, h, dd > ww, r() < 0.5 ? C('#8f9aa0') : C('#a8452f'), false);
    else clutter(bi, bj, ww, dd, h, r, base);
    if (s.kite && r() < s.kite) {
      const x = Math.round(sx(bi + 0.4, bj + 0.4)), y = Math.round(sy(bi + 0.4, bj + 0.4, h)), kc = pick(r, SAREE);
      person(bi + 0.4, bj + 0.4, pick(r, PCOL), h, 0.5);
      LN(x, y - 3, x + 8, y - 14, C('#e9e2d0'), bi + bj + 1);
      R(x + 7, y - 16, 3, 3, kc, bi + bj + 1.1);
    }
  }
  function lane(i, j, r, fr) {
    if (!fr(i, j, 1, 1)) return;
    gRect(i, j, 1, 1, T.LANE); claim(i, j, 1, 1);
    const u = r();
    if (u < 0.1) person(i + 0.2 + r() * 0.6, j + 0.3 + r() * 0.5, pick(r, PCOL));
    else if (u < 0.14) vehicle('rick', i + 0.5, j + 0.5, 0, r() < 0.5 ? 'i' : 'j');
  }
  function fill(i0, j0, i1, j1, sty, r, o) {
    o = o || {};
    const s = STY[sty], ok = o.ok;
    i0 = Math.max(0, i0); j0 = Math.max(0, j0); i1 = Math.min(GW, i1); j1 = Math.min(GH, j1);
    const fr = (i, j, w, d) => {
      if (!isFree(i, j, w, d)) return false;
      if (ok) for (let b = j; b < j + d; b++) for (let a = i; a < i + w; a++) if (!ok(a, b)) return false;
      return true;
    };
    if (!o.nolanes) {
      for (let li = i0 + 2 + ri(r, 3); li < i1 - 1; li += 5 + ri(r, 2)) for (let j = j0; j < j1; j++) lane(li, j, r, fr);
      for (let lj = j0 + 3 + ri(r, 3); lj < j1 - 1; lj += 6 + ri(r, 2)) for (let i = i0; i < i1; i++) lane(i, lj, r, fr);
    }
    if (s.chim) for (let n = 0; n < s.chim; n++) {
      for (let tries = 0; tries < 30; tries++) {
        const i = i0 + ri(r, Math.max(1, i1 - i0)), j = j0 + ri(r, Math.max(1, j1 - j0));
        if (fr(i, j, 1, 1)) { claim(i, j, 1, 1); chimney(i + 0.05, j + 0.05, 34 + ri(r, 12), BRICK); break; }
      }
    }
    for (let j = j0; j < j1; j++) for (let i = i0; i < i1; i++) {
      if (!fr(i, j, 1, 1)) continue;
      const nr = RD[j * GW + i - 1] || RD[j * GW + i + 1] || RD[(j - 1) * GW + i] || RD[(j + 1) * GW + i];
      if (r() < (nr ? 0.2 : o.treeP || 0.1)) { treeCell(i, j, r, !nr && r() < 0.4); continue; }
      let w = 1 + Math.max(ri(r, s.mw), ri(r, s.mw)), d = 1 + Math.max(ri(r, s.md), ri(r, s.md));
      if (s.minw) { w = Math.max(w, s.minw); d = Math.max(d, s.minw); }
      while (w > 1 && !fr(i, j, w, d)) w--;
      while (d > 1 && !fr(i, j, w, d)) d--;
      const low = !s.glass && !s.shed && (RD[j * GW + i - 1] || RD[(j - 1) * GW + i]);
      building(i, j, w, d, s, r, low ? Object.assign({ cap: 2 }, o) : o);
    }
  }

  /* ---------- global layout ---------- */
  function baseGround() {
    gRect(0, 0, GW, GH, T.PAVE);
    gFn(0, 0, GW, GH, (i, j) => (i > L.wb(j) && i < L.eb(j) ? T.WATER : 0));
    for (let b = 0; b < GH; b++) for (let a = 0; a < GW; a++) {
      for (let q = 0; q < 4; q++) { const j = b + (q + 0.5) / 4; if (a < L.eb(j) && a + 1 > L.wb(j)) { OCC[b * GW + a] = 1; break; } }
    }
    for (const rd of L.roads) {
      if (rd.id === 'chitpur') { road(rd.axis, rd.at, rd.from, rd.tramTo, rd.w, true); road(rd.axis, rd.at, rd.tramTo, rd.to, rd.w, false); }
      else road(rd.axis, rd.at, rd.from, rd.to, rd.w, !!rd.tram);
    }
  }

  function structures() {
    const asph = (x, y, fi, fj) => (fj > 0.9 && fj < 1.1 && (((fi * 2) | 0) & 1) ? C('#d8cfa8') : (hs(x, y) % 9 === 0 ? C('#3f3b46') : C('#4a4652')));
    /* Howrah Bridge */
    {
      const H = L.howrahBridge, j0 = H.j;
      box(13, j0, 10, 2, 2, 5, asph, STEEL, STEELD);
      claim(11, j0, 14, 2);
      for (let k = 0; k < 4; k++) {
        const iw = 11 + k * 0.5, ie = 24.5 - k * 0.5;
        box(iw, j0, 0.5, 2, Math.ceil(H.z(iw + 0.5)), 0, asph, STEEL, STEELD);
        box(ie, j0, 0.5, 2, Math.ceil(H.z(ie)), 0, asph, STEEL, STEELD);
      }
      const zT = H.deckZ + H.towerH, back = j0 + 0.15, front = j0 + 1.85;
      for (const ti of H.towers) {
        box(ti - 0.15, j0, 0.3, 0.3, zT, 0, STEEL, STEEL, STEELD);
        box(ti - 0.15, j0 + 1.7, 0.3, 0.3, zT, 0, STEEL, STEEL, STEELD);
        box(ti - 0.15, j0 + 0.3, 0.3, 1.4, 3, zT - 3, STEEL, STEEL, STEELD, { ns: 1 });
        box(ti - 0.15, j0 + 0.3, 0.3, 1.4, 2, zT - 18, STEEL, STEEL, STEELD, { ns: 1 });
        box(ti - 0.15, j0 + 0.3, 0.3, 1.4, 2, H.deckZ + 2, STEEL, STEEL, STEELD, { ns: 1 });
        line3([ti, back, zT - 3], [ti, front, zT - 18], STEELD, 0.2); line3([ti, front, zT - 3], [ti, back, zT - 18], STEELD, 0.2);
        line3([ti, back, zT - 18], [ti, front, H.deckZ + 4], STEELD, 0.2); line3([ti, front, zT - 18], [ti, back, H.deckZ + 4], STEELD, 0.2);
      }
      const zA = H.z(12) + 2, zB = H.z(24) + 2, mid = 23;
      const chord = (i) => (i < 14.5 ? lerp(zA, zT, (i - 12) / 2.5) : i <= 21.5 ? mid + (zT - mid) * Math.pow((i - 18) / 3.5, 2) : lerp(zT, zB, (i - 21.5) / 2.5));
      const bot = (i) => H.z(i) + (i >= 13 && i <= 23 ? 2 : 1);
      for (const [pj, c] of [[back, STEELD], [front, STEEL]]) {
        for (let i = 12; i < 24; i += 0.25) {
          line3([i, pj, chord(i)], [i + 0.25, pj, chord(i + 0.25)], c, 0.2);
          line3([i, pj, chord(i) - 1], [i + 0.25, pj, chord(i + 0.25) - 1], c, 0.2);
        }
        for (let i = 12; i <= 24; i += 0.5) {
          line3([i, pj, bot(i)], [i, pj, chord(i)], c, 0.2);
          if (i < 24) {
            line3([i, pj, bot(i)], [i + 0.5, pj, chord(i + 0.5)], c, 0.2);
            line3([i, pj, chord(i)], [i + 0.5, pj, bot(i + 0.5)], c, 0.2);
          }
        }
        line3([12, pj, bot(12)], [24, pj, bot(24)], c, 0.2);
      }
      for (const ti of H.towers) { line3([ti, back, zT], [ti, front, zT], STEELD, 0.25); line3([ti, back, zT + 1], [ti, front, zT + 1], STEEL, 0.25); glow(ti, front, zT + 3, C('#ffe9a8')); }
      for (let i = 12.5; i < 24; i += 0.5) glow(i, front, chord(i) + 0.5, C('#ffe9a8'));
      for (let i = 13; i <= 23; i += 1) glow(i, front, H.deckZ + 3, C('#ffd27a'));
    }
    /* Vidyasagar Setu */
    {
      const S = L.setu, j0 = S.j, w = S.w;
      box(0, j0, 14, w, 2, 7, asph, C('#cfc9bd'), C('#a39d91'));
      for (let k = 0; k < 5; k++) box(14 + k, j0, 1, w, Math.max(1, Math.ceil(S.z(14.5 + k))), 0, asph, C('#cfc9bd'), C('#a39d91'));
      claim(0, j0, 20, w);
      const conc = C('#ece8de'), concL = C('#d2ccbf'), concD = C('#b3ad9f'), top = S.deckZ + S.pylonH;
      for (const pi of S.pylons) {
        box(pi - 0.2, j0, 0.4, 0.4, top, 0, conc, concL, concD);
        box(pi - 0.2, j0 + w - 0.4, 0.4, 0.4, top, 0, conc, concL, concD);
        box(pi - 0.2, j0 + 0.4, 0.4, w - 0.8, 3, top - 12, conc, concL, concD, { ns: 1 });
        box(pi - 0.2, j0 + 0.4, 0.4, w - 0.8, 2, top - 3, conc, concL, concD, { ns: 1 });
        glow(pi, j0 + 0.2, top + 2, C('#ff6a5a')); glow(pi, j0 + w - 0.2, top + 2, C('#ff6a5a'));
        for (let k = 1; k < 5; k++) { glow(pi - 0.9 * k, j0 + 0.1, S.deckZ + 2, C('#ffe9a8')); glow(pi + 0.9 * k, j0 + 0.1, S.deckZ + 2, C('#ffe9a8')); }
        for (const pj of [j0 + 0.2, j0 + w - 0.2]) for (const side of [-1, 1]) for (let k = 1; k <= 6; k++) {
          const i = pi + side * 0.75 * k;
          if (i < 0.2 || i > 14) continue;
          line3([pi, pj, top - 2.4 * (6 - k) - 1], [i, pj, S.deckZ + 2], C('#dfe3e6'), 0.2);
        }
      }
    }
    /* Metro viaduct */
    {
      const V = L.viaduct;
      claim(115, V.j0, 1, V.j1 - V.j0);
      gRect(115, V.j0, 1, V.j1 - V.j0, T.LANE);
      box(V.i, V.j0, V.w, V.j1 - V.j0, 2, V.z - 2, C('#d9d4ca'), C('#bdb7ab'), C('#8e897e'));
      for (let j = V.j0 + 1; j < V.j1; j += 3) box(V.i + 0.15, j, 0.5, 0.5, V.z - 2, 0, C('#cfc9bd'), C('#bdb7ab'), C('#8e897e'));
    }
    /* Gariahat flyover */
    {
      const F = L.flyover, a = asph;
      ground(F.i, F.j0, 1, F.j1 - F.j0, T.LANE);
      box(F.i, 78, 1, 12, 2, 5, a, STEEL, STEELD);
      for (let k = 0; k < 4; k++) {
        const jn = 76 + k * 0.5, js = 91.5 - k * 0.5;
        box(F.i, jn, 1, 0.5, Math.ceil(F.z(jn + 0.5)), 0, a, STEEL, STEELD);
        box(F.i, js, 1, 0.5, Math.ceil(F.z(js)), 0, a, STEEL, STEELD);
      }
      for (let j = 79; j < 90; j += 2.5) box(F.i + 0.3, j, 0.4, 0.4, 5, 0, C('#cfc9bd'), C('#bdb7ab'), C('#8e897e'));
    }
  }

  function slab() {
    const strata = ['#6b8f3f', '#7a5a38', '#8a6540', '#a97c4c', '#b78d58', '#8d6a43', '#7a5a3a', '#6a503a', '#594632'];
    const sc = strata.map(C), water = C('#7d8a5b'), waterD = C('#66744a');
    const w0 = L.wb(GH), w1 = L.eb(GH);
    const earth = (t, x, y) => {
      const k = t < 1 ? 0 : t < 3 ? 1 : t < 6 ? 2 : t < 9 ? 3 : t < 11 ? 4 : t < 13 ? 5 : t < 15 ? 6 : t < 17 ? 7 : 8, n = hs(x, y);
      let c = sc[k]; if (n % 7 === 0) c = sh(c, 0.88); else if (n % 11 === 0) c = sh(c, 1.1);
      return c;
    };
    const left = (a, t, h, x, y) => { const i = a / E.HW; if (i > w0 && i < w1) return t < 3 ? water : t < 8 ? waterD : sh(waterD, 0.8); return earth(t, x, y); };
    const right = (a, t, h, x, y) => sh(earth(t, x, y), 0.76);
    box(0, 0, GW, GH, 18, -18, null, left, right);
  }

  /* ---------- districts ---------- */
  function r1c1(r) {
    // west bank
    for (let j = 0; j < 23; j++) {
      if (j % 4 === 1) { B(0.1, j + 0.2, 1.4, 1.5, 3, 0, { mats: [C('#b38a5a'), C('#8a6a43')], roof: null }); gable(0.1, j + 0.2, 1.4, 1.5, 3, 3, false, C('#c9a55a')); }
      else if (!OCC[j * GW + 1]) { tree(1, j, 2, j * 3); claim(1, j, 1, 1); }
      if (j % 4 === 3) { tree(0, j, 2, j + 9); claim(0, j, 1, 1); }
    }
    B(0.1, 8, 2.2, 3, 7, C('#a8452f'), { cw: 6, ww: 3, wh: 2, wy: 3, win: BLK });
    chimney(0.7, 12.2, 42, BRICK);
    // clay patches and ghat
    groundFn(11.5, 0, 23, 23, () => 0);
    gRect(14, 1, 3, 2, T.CLAY); gRect(19, 12, 3, 2, T.CLAY);
    ground(10.5, 8, 2.6, 6, T.STEPS);
    B(13.4, 9, 1.4, 1.4, 6, WH, { mats: [WH, sh(WH, 0.74)], roof: sh(WH, 0.96) });
    spire(14.1, 9.7, 6, 0.75, 10, C('#f08a24'));
    line3([14.1, 9.7, 16], [14.1, 9.7, 24], C('#5a4a3a'), 0.12); for (let k = 0; k < 3; k++) pt(14.1 + (k + 1) * 0.125, 9.7, 23 - (k > 1 ? 0 : 0) - 0, C('#e2452f'), 0.14);
    // workshops
    const idol = ['...g...', '..gfg..', 'g..g..g', 'gg.g.gg', '.ggggg.', '..ggg..', '..ggg..', 'sssssss'];
    let n = 0;
    for (let k = 0; k < 6; k++) {
      const j = 1 + 3.5 * k;
      for (const [i, skip] of [[12.4, j > 7.5 && j < 14.5], [15.6, false], [19.0, false]]) {
        if (skip) continue;
        const tc = TARP[n++ % TARP.length], base = C('#9c7a55');
        B(i, j, 2.2, 1.5, 5, base, { mats: [openF(base), sh(base, 0.72)], roof: stripeM(tc, sh(tc, 0.82), true, 3) });
        ground(i - 0.2, j + 1.5, 2.6, 1.9, T.CLAY);
        for (let q = 0; q < 3; q++) {
          const painted = (n + q) % 4 === 0, pc = (n + q) % 8 === 0 ? C('#e2452f') : GOLD;
          stamp(i + 0.35 + q * 0.7, j + 2.1 + (q & 1) * 0.35, 0, idol, { g: painted ? pc : C('#a8a090'), f: painted ? C('#f1c6a8') : C('#d9cdb5'), s: C('#c9a55a') }, 0.6);
        }
      }
    }
    for (const [i, j, ax] of [[5.5, 4, 'j'], [7.4, 10.5, 'j'], [4.8, 16, 'j'], [8.5, 20, 'i'], [6.5, 1.5, 'i']]) vehicle('boat', i, j, 0, ax);
    claim(11, 0, 1, 23);
    fill(11, 0, 23, 23, 'north', r);
  }

  function r1c2(r) {
    const red = C('#b23a34'), grn = C('#2f6b4f'), wo = { cw: 5, ww: 2, wh: 3, win: grn, band: CREAM, cornice: CREAM, plinth: CREAM, litP: 3 }, rf = roofM(C('#8a3a30'));
    ground(33.5, 9.5, 5, 5.6, T.LAWN); ground(35.5, 9.5, 1, 5.6, T.REDPATH);
    B(31, 7, 10, 2.5, 14, red, Object.assign({ roof: rf }, wo));
    B(31, 9.5, 2.5, 5.6, 14, red, Object.assign({ roof: rf }, wo));
    B(38.5, 9.5, 2.5, 5.6, 14, red, Object.assign({ roof: rf }, wo));
    tree(34, 11, 0, 5); tree(37, 12, 4, 6);
    B(36.7, 13.2, 0.4, 0.4, 3, WH, { mats: [WH, sh(WH, 0.7)], roof: WH }); pt(36.9, 13.4, 5, C('#a8714a'), 0.3); pt(36.9, 13.4, 4, WH, 0.3);
    crowd(33.8, 12, 4.6, 2.8, 6, r, PCOL);
    for (let k = 0; k < 9; k++) {
      const aw = AW[k % AW.length], base = C(['#f6d48a', '#f3c6c0', '#f1e6c8'][k % 3]);
      B(44.2, 1 + k * 2.4, 2.5, 2.1, 9, base, { shop: [aw[0], aw[1], C('#3a2418')], cw: 4, win: C('#2f6b4f'), band: CREAM });
    }
    fill(25, 0, 47, 23, 'north', r);
  }

  function r1c3(r) {
    ground(59, 3, 9, 10, T.PLAZA); ground(60, 4, 7, 8, T.POND);
    for (const [i, j] of [[61.5, 5.5], [63.5, 6.5], [64.7, 9], [62, 8.8], [65.5, 5.2], [60.8, 10.5]]) person(i, j, pick(r, PCOL), 0, 0.3);
    road('j', 58, 0, 23, 1, false);
    ground(51, 6, 7, 3, T.LAWN);
    const pr = C('#f4f0e4');
    B(51, 3, 7, 3, 12, pr, { mats: pairM(() => colM(pr, { ch: 6, per: 4, dark: C('#6a7a86'), win: C('#6a7a86'), cornice: pr })), roof: sh(pr, 0.9) });
    for (let k = 0; k < 3; k++) tree(51 + k * 2.5 | 0, 8, 3 + (k & 1) * 3, k);
    B(53, 12, 4, 3, 16, C('#f0dc9a'), { rh: 7, wy: 1, wh: 4, cw: 5, win: C('#5a4a38'), cornice: C('#c9a050'), band: C('#c9a050'), litP: 2, roof: roofM(C('#c9a050')) });
    for (let j = 6; j < 23; j++) for (const ci of [57, 59]) {
      if (!isFree(ci, j, 1, 1)) continue;
      const c = pick(r, TARP);
      claim(ci, j, 1, 1);
      box(ci + 0.1, j + 0.1, 0.8, 0.8, 3, 0, stripeM(c, C('#f1ead8'), (j & 1) === 0, 3), (a, t) => (t === 0 ? c : hs(a, ci * 7 + j) % 4 === 0 ? C('#4a3220') : BOOK[hs(a, j) % BOOK.length]), (a, t) => sh(t === 0 ? c : BOOK[hs(a, j + 3) % BOOK.length], 0.75), { ns: 1 });
      const lx = ci === 57 ? 58.1 : 58.7;
      for (let q = 0; q < 4; q++) { pt(lx + (ci === 57 ? 0 : -0.1), j + 0.15 + q * 0.2, 0, BOOK[(q + j) % BOOK.length], 0.3); if (q & 1) pt(lx, j + 0.15 + q * 0.2, 1, BOOK[(q + j + 2) % BOOK.length], 0.3); }
    }
    for (let j = 1; j < 23; j += 1.7) { person(58.15 + r() * 0.2, j + r() * 0.5, pick(r, PCOL)); person(58.7 + r() * 0.2, j + 0.8 + r() * 0.4, pick(r, PCOL)); }
    fill(49, 0, 71, 23, 'north', r, { shopP: 0.5 });
  }

  function r1c4(r) {
    for (let c = 76; c < 90; c++) ground(c, 0, 1, 9, ((c - 76) & 1) === 0 ? T.RAILJ : T.PLAZA);
    ground(76, 9, 14, 1, T.PLAZA);
    vehicle('train', 78.5, 5.0, 0, 'j'); vehicle('train', 82.5, 5.3, 0, 'j', 1); vehicle('train', 86.5, 4.7, 0, 'j');
    const tin = C('#8f9aa0');
    for (let c = 77; c < 90; c += 2) {
      gable(c - 0.4, 0.2, 1.8, 5.2, 4, 11, true, c % 4 === 1 ? tin : C('#a3adb3'), true);
      for (const j of [0.7, 2.6, 4.8]) for (const o of [-0.3, 1.1]) box(c + o, j, 0.12, 0.12, 11, 0, STEELD, STEELD, STEELD, { ns: 1 });
    }
    const bc = BRICK;
    B(75, 10, 16, 3, 12, bc, { mats: pairM(() => colM(bc, { ch: 6, per: 4, colc: CREAM, dark: C('#3a2a28'), cw: 4, win: CREAM, band: CREAM, cornice: CREAM, litP: 3 })), roof: roofM(C('#8d4a38')) });
    B(81.8, 10, 2.4, 3, 20, bc, { cw: 4, win: CREAM, band: CREAM, cornice: CREAM, litP: 2 });
    // short flyover at j=16
    claim(76, 16, 16, 1); ground(76, 16, 16, 1, T.LANE);
    const asph = C('#4a4652');
    box(78, 16, 12, 1, 2, 5, asph, STEEL, STEELD);
    for (let k = 0; k < 4; k++) { box(76 + k * 0.5, 16, 0.5, 1, Math.ceil(lerp(0, 7, (k * 0.5 + 0.5) / 2)), 0, asph, STEEL, STEELD); box(91.5 - k * 0.5, 16, 0.5, 1, Math.ceil(lerp(7, 0, k * 0.5 / 2)), 0, asph, STEEL, STEELD); }
    for (let i = 79; i < 90; i += 3) box(i + 0.3, 16.3, 0.4, 0.4, 5, 0, C('#cfc9bd'), C('#bdb7ab'), C('#8e897e'));
    stalls(73, 13, 95, 23, r, { rs: 2, p: 0.8 });
    crowd(73, 13, 21, 10, 90, r, PCOL);
    fill(73, 0, 95, 23, 'burra', r);
  }

  function r1c5(r) {
    ground(103, 5, 12, 13, T.DIRT); ground(113, 14, 4, 4, T.DIRT);
    const mag = C('#c8307a'), teal = C('#1f9a9a'), gold = GOLD;
    B(105, 7, 6, 5, 12, mag, { mats: pairM(() => patM(mag, gold, teal)), roof: stripeM(gold, C('#c8307a'), false, 4) });
    B(106, 8, 4, 3, 8, mag, { z: 12, mats: pairM(() => patM(teal, gold, mag)), roof: stripeM(gold, teal, true, 4) });
    B(107, 8.6, 2, 1.8, 6, mag, { z: 20, mats: pairM(() => patM(mag, gold, teal)), roof: gold });
    spire(108, 9.5, 26, 0.7, 15, gold);
    for (const [ci, cj] of [[105, 7], [110, 7]]) { spire(ci + 0.5, cj + 0.5, 12, 0.5, 8, gold); }
    const arch = ['..ggggggg..', '.gkkkkkkkg.', 'gkkkkfkkkkg', 'gkkkyyykkkg', 'gkkyyryykkg', 'gkyyyryyykg', 'gkkyyryykkg', 'gkkrrrrrkkg', 'gkkkkkkkkkg', 'ggggggggggg'];
    stamp(108, 12.02, 0, arch, { g: gold, k: C('#3a1a30'), f: C('#f1c6a8'), y: C('#f6d030'), r: C('#d8302a') }, 1.0);
    B(106, 17.2, 0.5, 0.5, 15, gold, { mats: [gold, sh(gold, 0.7)] }); B(110.2, 17.2, 0.5, 0.5, 15, gold, { mats: [gold, sh(gold, 0.7)] });
    B(106, 17.2, 4.7, 0.5, 3, mag, { z: 15, mats: pairM(() => patM(mag, gold, teal)), roof: gold, nc: 1 });
    for (let k = 0; k <= 15; k++) glow(106.2 + k * 0.3, 17.55, 14.6, [C('#ffd24a'), C('#ff5a8a'), C('#6af0e0')][k % 3]);
    const poles = [[103.3, 5.3], [109, 5.3], [114.6, 5.3], [103.3, 11], [103.3, 17.4], [114.6, 11]];
    for (const [i, j] of poles) pole(i, j, 14);
    const bc = [C('#ffd24a'), C('#ff5a8a'), C('#6af0e0'), C('#a0f060'), C('#ff8a3a')];
    bulbs([103.3, 5.3, 14], [109, 5.3, 14], 2.5, bc); bulbs([109, 5.3, 14], [114.6, 5.3, 14], 2.5, bc);
    bulbs([103.3, 5.3, 14], [103.3, 11, 14], 2.5, bc); bulbs([103.3, 11, 14], [103.3, 17.4, 14], 2.5, bc); bulbs([114.6, 5.3, 14], [114.6, 11, 14], 2.5, bc);
    bulbs([103.3, 11, 14], [105, 7, 12], 1.5, bc); bulbs([114.6, 11, 14], [110.6, 8, 12], 1.5, bc); bulbs([103.3, 17.4, 14], [106, 17.4, 15], 1, bc);
    for (let k = 0; k < 10; k++) { smallStall(103 + k * 1.15 | 0, 5, r); }
    for (let k = 0; k < 6; k++) { const i = 103, j = 6 + k * 1.8; if (isFree(i, j | 0, 1, 1)) smallStall(i, j | 0, r); }
    for (let k = 0; k < 5; k++) { const j = 6 + k * 1.6 | 0; if (j < 13 && isFree(114, j, 1, 1)) smallStall(114, j, r); }
    crowd(104, 6, 10, 11.5, 230, r, PCOL);
    for (let k = 0; k < 4; k++) { person(109 + k * 0.28, 14.3 + (k & 1) * 0.3, C('#f1ead8'), 0, 0.4); pt(109 + k * 0.28, 14.7 + (k & 1) * 0.3, 2, C('#d8302a'), 0.5); pt(109 + k * 0.28, 14.7 + (k & 1) * 0.3, 3, C('#d8302a'), 0.5); }
    fill(97, 0, 120, 23, 'north', r);
  }

  function r2c1(r) {
    ground(0, 26, 1, 9, T.RAILJ); ground(1, 26, 1, 9, T.PLAZA); ground(2, 26, 1, 9, T.RAILJ);
    ground(3, 25, 4, 1, T.RAILI); ground(3, 27, 4, 1, T.RAILI);
    vehicle('train', 0.5, 30.5, 0, 'j'); vehicle('train', 2.5, 29.5, 0, 'j', 1);
    gable(0, 26.3, 3, 8.4, 4, 11, true, C('#8f9aa0'), true);
    for (const j of [26.8, 30.5, 34.2]) box(1.4, j, 0.15, 0.15, 11, 0, STEELD, STEELD, STEELD, { ns: 1 });
    B(3, 28, 4.5, 6, 12, BRICK, { cw: 5, ww: 2, wh: 3, win: C('#e8d9b5'), band: C('#e8d9b5'), cornice: C('#e8d9b5'), litP: 3, roof: roofM(C('#8d4a38')) });
    for (const [i, j] of [[3, 28], [6.5, 28], [3, 33], [6.5, 33]]) { B(i, j, 1, 1, 18, BRICK, { cw: 4, ww: 1, wh: 3, win: C('#e8d9b5'), band: C('#e8d9b5'), cornice: C('#e8d9b5'), litP: 3, roof: CREAM }); pyr(i + 0.1, j + 0.1, 0.8, 0.8, 5, 18, C('#e8d9b5')); }
    clock(7.5, 31, 8);
    groundFn(7.6, 28.5, 15, 35, (i, j) => (i > 7.6 && i < L.wb(j) - 0.1 && j > 28.5 && j < 35 ? T.PLAZA : 0));
    for (let k = 0; k < 5; k++) vehicle('taxi', 8.3, 29.2 + k * 1.1, 0, 'j');
    for (let k = 0; k < 4; k++) vehicle('taxi', 9.8, 32 + k * 1.05, 0, 'j');
    vehicle('taxi', 11.3, 33.6, 0, 'j');
    crowd(8, 29, 3, 5, 14, r, PCOL);
    const jw = L.wb(31);
    box(jw - 0.8, 31, 3.6, 0.7, 1, 0, WOOD, C('#6a4a32'), C('#52382a'));
    vehicle('ferry', jw + 4.2, 33.4, 0, 'j');
    fill(0, 25, 15, 47, 'howrah', r);
  }

  function r2c2(r) {
    const eb = L.eb;
    groundFn(14, 38, 23, 47, (i, j) => (i > eb(j) + 0.1 && i < 23 ? T.FLOWER : 0));
    for (let k = 0; k < 46; k++) {
      const j = 38.3 + r() * 8.5, i = eb(j) + 0.5 + r() * (22.4 - eb(j) - 0.5);
      if (i < eb(j) + 0.4 || i > 22.6) continue;
      dome(i, j, 0, 0.26 + r() * 0.18, 3 + ri(r, 3), pick(r, [C('#f08a24'), C('#f6c832'), C('#e8761c'), C('#f9d84a')]));
    }
    for (let k = 0; k < 9; k++) {
      const j = 38.4 + (k % 4) * 2.2, i = eb(j) + 1 + ((k / 4) | 0) * 2.4;
      if (i > 21.6) continue;
      box(i, j, 0.9, 0.7, 3, 0, C('#e8892a'), C('#c06a22'), C('#a05a1c'), { ns: 1 });
      for (let q = 0; q < 4; q++) { const gc = q & 1 ? C('#f08a24') : C('#f6c832'); line3([i + 0.1 + q * 0.22, j + 0.8, 7], [i + 0.1 + q * 0.22, j + 0.8, 1], gc, 0.3); }
    }
    for (let k = 0; k < 70; k++) { const j = 38.2 + r() * 8.6, i = 14 + r() * 9; if (i > eb(j) + 0.3 && i < 22.8) person(i, j, pick(r, PCOL)); }
    // east bank land north of the flower market
    fill(15, 25, 23, 38, 'burra', r);
    // Nakhoda Masjid
    const rs = C('#b5523c');
    B(37, 27, 7, 5, 10, rs, { cw: 4, win: C('#e8d9b5'), band: C('#d8b090'), cornice: C('#d8b090'), litP: 3 });
    drum(40.5, 29.5, 10, 1.6, 2, C('#c9a07a'), C('#c9a07a'));
    dome(40.5, 29.5, 12, 1.6, 9, C('#2f8f5a'), { rib: 3 });
    minaret(37.2, 31.2, 36, rs, C('#2f8f5a')); minaret(42.7, 31.2, 36, rs, C('#2f8f5a'));
    stalls(25, 25, 47, 47, r, { p: 0.18, rs: 3 });
    fill(25, 25, 47, 47, 'burra', r);
  }

  function r2c3(r) {
    ground(55, 32, 10, 10, T.LAWN); ground(56, 33, 8, 8, T.POND);
    for (let b = 32; b < 42; b++) for (let a = 55; a < 65; a++) if ((a === 55 || a === 64 || b === 32 || b === 41) && (a + b) % 2 === 0) tree(a, b, [3, 0, 6, 7, 1][(a * 3 + b) % 5], a * 11 + b);
    for (const [i, j] of [[55.5, 36], [64.5, 38], [60, 32.5], [58, 41.4], [62, 41.4], [55.4, 39.5], [64.6, 34]]) person(i, j, pick(r, [C('#f1ead8'), C('#2f66b0'), C('#d8d0c0'), C('#4a5a6a')]), 0, 0.5);
    const rd = C('#b23a34'), wo = { cw: 5, ww: 2, wh: 3, win: CREAM, band: C('#f1ead8'), cornice: C('#f1ead8'), litP: 3 };
    B(53, 27, 14, 3, 13, rd, Object.assign({ roof: roofM(C('#8a3a30')) }, wo));
    B(57.5, 27.5, 6, 2.5, 16, rd, Object.assign({ roof: roofM(C('#8a3a30')), nc: 1 }, wo));
    gable(57.5, 27.5, 6, 2.5, 4, 16, true, WH);
    B(58, 30, 5, 1, 10, WH, { mats: pairM(() => colM(WH, { ch: 9, per: 3, dark: C('#6a3a38'), cornice: WH })), roof: WH });
    gable(58, 30, 5, 1, 3, 10, true, WH);
    for (let k = 0; k < 14; k++) if (k < 5 || k > 8) { pt(53.5 + k, 29.85, 14, WH, 0.3); pt(53.5 + k, 29.85, 15, WH, 0.3); }
    // GPO
    B(50, 34, 4, 5, 12, WH, { cw: 4, win: C('#7a8a96'), cornice: WH, band: C('#e8e0d0'), litP: 3 });
    drum(52, 36.5, 12, 1.6, 5, WH, WH); dome(52, 36.5, 17, 1.6, 10, WH, { rib: 4 }); line3([52, 36.5, 27], [52, 36.5, 31], GOLD, 0.2);
    // St Andrew's
    B(67, 27, 2.6, 4.2, 9, WH, { cw: 4, ww: 1, wh: 4, win: C('#7a8a96'), litP: 0 });
    gable(67, 27, 2.6, 4.2, 4, 9, true, C('#8a8f9a'));
    churchSpire(67.6, 31, 1.3, 1.3, 18, 14, WH, C('#8a8f9a'));
    // tram terminus
    road('i', 44, 50, 70, 1, true);
    vehicle('tram', 54, 44.5, 0, 'i'); vehicle('tram', 60, 44.5, 0, 'i'); vehicle('tram', 66, 44.5, 0, 'i');
    stalls(49, 25, 71, 47, r, { p: 0.12, rs: 3 });
    fill(49, 25, 71, 47, 'office', r);
  }

  function r2c4(r) {
    ground(74, 26, 8, 7, T.LAWN);
    const cr = C('#f1e6c8');
    B(75.5, 28, 5, 3, 9, cr, { cw: 4, win: C('#7a8a96'), band: WH, cornice: WH, litP: 3 });
    drum(78, 29.5, 9, 0.8, 2, WH, WH); dome(78, 29.5, 11, 0.9, 6, WH);
    for (let k = 0; k < 8; k++) tree(74 + k, 26, 0, k), tree(74 + k, 32, 3, k + 4);
    ground(74, 40, 5, 5, T.GRASS);
    const mx = 76.5, mj = 42.5;
    drum(mx, mj, 0, 0.85, 5, WH, WH); drum(mx, mj, 5, 0.45, 17, WH, WH);
    drum(mx, mj, 22, 0.8, 2, WH, C('#d8d2c0')); drum(mx, mj, 24, 0.4, 14, WH, WH);
    drum(mx, mj, 38, 0.7, 2, WH, C('#d8d2c0')); drum(mx, mj, 40, 0.35, 8, WH, WH);
    dome(mx, mj, 48, 0.42, 6, WH); line3([mx, mj, 54], [mx, mj, 58], GOLD, 0.2);
    ground(77, 40, 9, 7, T.ROAD); road('i', 41, 77, 86, 1, true); road('i', 44, 77, 86, 1, true);
    vehicle('tram', 80, 41.5, 0, 'i'); vehicle('tram', 83.5, 44.5, 0, 'i');
    vehicle('bus', 81, 42.5, 0, 'i', C('#c8382e')); vehicle('bus', 84, 40.5, 0, 'i'); vehicle('bus', 80, 45.5, 0, 'i', C('#2f6fc0')); vehicle('bus', 84.5, 42.5, 0, 'i', C('#c8382e'));
    const bc = C('#b4503a');
    B(84, 30, 8, 6, 9, bc, { cw: 4, win: CREAM, band: CREAM, cornice: CREAM, litP: 3, shop: [C('#e8892a'), C('#f6d255'), C('#2a2224')], roof: C('#8d4a38') });
    gable(84, 30, 4, 6, 4, 9, true, C('#c9603a')); gable(88, 30, 4, 6, 4, 9, true, C('#c9603a'));
    B(90.8, 29.8, 1.4, 1.4, 24, bc, { cw: 4, ww: 1, wh: 3, win: CREAM, band: CREAM, litP: 0, roof: sh(bc, 0.8) });
    pyr(90.8, 29.8, 1.4, 1.4, 8, 24, C('#6b3a2c'));
    clock(91.5, 31.2, 18);
    B(73, 33, 2, 6, 12, WH, { mats: pairM(() => colM(WH, { ch: 5, per: 3, dark: C('#6a7a86'), win: C('#6a7a86'), cornice: WH, litP: 3 })), roof: WH });
    stalls(73, 25, 95, 47, r, { p: 0.3, rs: 2 });
    fill(73, 25, 95, 47, 'burra', r);
  }

  function r2c5(r) {
    let i = 97;
    const names = ['#f3ead6', '#e8d9b5', '#d9c3a0', '#c9d6cf', '#e6b8a8'];
    let n = 0;
    while (i < 116) {
      const w = 2.6 + r() * 1.0, aw = AW[n % AW.length], flur = Math.abs(i - 109) < 1.6;
      const base = C(flur ? '#f2b8c6' : names[n % 5]);
      const sc = flur ? [C('#d83a4a'), C('#ffffff'), C('#3a2418')] : [aw[0], aw[1], C('#3a2418')];
      const hh = flur ? 18 : 16 + ri(r, 2) * 6;
      B(i, 43, w, 4, hh, base, { cw: 4, win: C(['#3d6e7a', '#2f5f4a', '#a8453a'][n % 3]), band: sh(base, 0.84), cornice: flur ? WH : sh(base, 1.1), shop: sc, litP: 2, roof: roofM(sh(base, 0.8)) });
      clutter(i + 0.15, 43.15, w - 0.3, 3.7, hh, r, base);
      i += w; n++;
    }
    ground(104, 39, 5, 4, T.LAWN);
    box(106.4, 40.85, 0.3, 0.3, 4, 0, C('#6b4a33'), C('#6b4a33'), C('#4a3322'), { ns: 1 });
    pyr(105.3, 39.7, 2.6, 2.6, 12, 3, C('#2f7f45')); pyr(105.6, 40, 2, 2, 10, 11, C('#3a8f50')); pyr(105.95, 40.35, 1.3, 1.3, 9, 19, C('#46a05a'));
    const xm = [C('#e2452f'), C('#f4c531'), C('#2f66b0'), C('#f2f0e0'), C('#e48fb0')];
    for (let k = 0; k < 34; k++) {
      const t = k % 3, hsz = [1.3, 1.0, 0.65][t], zt = [3, 11, 19][t], ht = [12, 10, 9][t], ci = 106.6, cj = 41, a = k * 2.399, rho = hsz * (0.35 + ((k * 7) % 5) / 8);
      const di = Math.cos(a) * rho, dj = Math.sin(a) * rho, rr = Math.max(Math.abs(di), Math.abs(dj));
      glow(ci + di, cj + dj, zt + ht * (1 - rr / hsz) + 0.5, xm[k % 5]);
    }
    for (const [dx, dy] of [[0, 0], [1, 0], [-1, 0], [0, 1], [0, -1]]) { const x = Math.round(sx(106.6, 40.9)) + dx, y = Math.round(sy(106.6, 40.9, 30)) + dy; R(x, y, 1, 1, GOLD, 106.6 + 40.9 + 0.7); }
    light(Math.round(sx(106.6, 40.9)), Math.round(sy(106.6, 40.9, 30)), GOLD, 106.6 + 40.9 + 0.7);
    ground(100, 40, 3, 3, T.PLAZA);
    person(104.4, 42.6, C('#d8302a'), 0, 0.5); pt(104.4, 42.6, 3, C('#f1ead8'), 0.6);
    for (let k = 0; k < 5; k++) person(100.4 + k * 0.45, 41 + (k & 1) * 0.6, [C('#1f2a44'), C('#f1ead8'), C('#8a3f8f')][k % 3], 0, 0.5);
    for (let k = 0; k < 3; k++) pt(100.6 + k * 0.5, 42.2, 1, GOLD, 0.6);
    const fc = [C('#ffd24a'), C('#ff5a8a'), C('#6af0e0'), C('#a0f060'), C('#ff8a3a'), C('#ffffff')];
    for (let ci = 98; ci <= 116; ci += 2) {
      for (let s = 0; s <= 10; s++) { const j = 47 + s * 0.2; glow(ci, j, 12 - 3.4 * Math.sin(Math.PI * s / 10), fc[(s + ci) % fc.length]); }
    }
    B(111, 30, 3, 5, 9, C('#dcdad2'), { cw: 4, ww: 1, wh: 4, win: C('#6a7a86'), litP: 0 });
    gable(111, 30, 3, 5, 4, 9, true, C('#8a8f9a'));
    churchSpire(111.8, 28.6, 1.4, 1.4, 20, 15, C('#dcdad2'), C('#8a8f9a'));
    crowd(98, 44, 18, 4, 20, r, PCOL);
    fill(97, 25, 120, 43, 'park', r);
  }

  function r3c1(r) {
    gRect(12, 49, 11, 22, T.GRASS);
    groundFn(10, 49, 15, 71, (i, j) => (i > L.eb(j) + 0.1 && i < L.eb(j) + 1.3 ? T.PLAZA : 0));
    const FC = [17.5, 59.5], ks = 0.78;
    const rho = (i, j) => { const di = i - FC[0], dj = j - FC[1]; return Math.hypot(di, dj) / (1 + 0.22 * Math.cos(5 * Math.atan2(dj, di))) / ks; };
    const ft = (i, j) => { if (i <= L.eb(j) + 0.2 || i >= 23) return 0; const p = rho(i, j); return p < 4.3 ? T.LAWN : p < 4.9 ? T.BRICK : p < 5.6 ? T.MOAT : 0; };
    groundFn(11, 52, 24, 67, ft);
    for (const [i, j, w, d] of [[15.9, 57.4, 1.5, 0.8], [18, 57.4, 1.5, 0.8], [15.9, 61.0, 1.5, 0.8], [18, 61.0, 1.5, 0.8]]) {
      B(i, j, w, d, 3, C('#f1e6c8'), { mats: [C('#e8dcc0'), C('#b8ac90')], roof: null, nc: 1 });
      gable(i, j, w, d, 3, 3, false, C('#b8402e'));
    }
    line3([17.5, 59.5, 0], [17.5, 59.5, 24], C('#e9e2d0'), 0.15);
    for (let k = 0; k < 3; k++) for (let q = 0; q < 3; q++) pt(17.5 + (q + 1) * 0.125, 59.5, 23 - k, [C('#f08a24'), C('#f1ead8'), C('#2f8f5a')][k], 0.2);
    for (let j = 50; j < 70; j += 2.5) { const i = L.eb(j) + 1.1; lamp(i, j); }
    for (let k = 0; k < 8; k++) person(L.eb(50 + k * 2.5) + 0.5 + r() * 0.5, 50 + k * 2.4, pick(r, PCOL), 0, 0.5);
    vehicle('ship', 7, 62.5, 0, 'j');
    for (let j = 49; j < 71; j++) { if (!OCC[j * GW + 0]) { tree(0, j, j % 3 === 0 ? 0 : 2, j); claim(0, j, 1, 1); } if (!OCC[j * GW + 1] && j % 2) { tree(1, j, 2, j + 5); claim(1, j, 1, 1); } }
    maidan(12, 49, 23, 71, r, { tp: 0.3 });
  }

  function r3c2(r) {
    gRect(25, 49, 22, 22, T.GRASS);
    const rd = C('#b23a34'), wo = { cw: 4, ww: 2, wh: 4, wy: 1, rh: 7, win: C('#f1e6c8'), band: CREAM, cornice: CREAM, litP: 3 };
    B(27, 50, 9, 4, 14, rd, Object.assign({ roof: roofM(C('#6a4a40')) }, wo));
    B(30.75, 53, 1.5, 1.5, 26, rd, { cw: 4, ww: 1, wh: 4, win: CREAM, band: CREAM, cornice: CREAM, litP: 2, roof: C('#6a4a40') });
    spire(31.5, 53.75, 26, 0.9, 16, C('#b8b0a0'));
    for (const [i, j] of [[27, 50], [35.1, 50], [27, 53.1], [35.1, 53.1]]) { B(i, j, 0.9, 0.9, 20, rd, { cw: 4, ww: 1, wh: 3, win: CREAM, band: CREAM, litP: 0, roof: sh(rd, 0.8) }); spire(i + 0.45, j + 0.45, 20, 0.5, 7, C('#b8b0a0')); }
    // Eden Gardens
    const ci = 36, cj = 61.5;
    groundDisc(ci, cj, 7.5, 6.5, T.PAVE);
    gDisc(ci, cj, 5, 4.2, T.FIELD); gRect(34, 61.1, 4, 0.8, T.PITCH);
    const q = (a, b) => Math.sqrt(((a - ci) / 7.5) ** 2 + ((b - cj) / 6.5) ** 2);
    const cc = C('#cfc8bb');
    for (let b = 54; b < 70; b++) for (let a = 28; a < 45; a++) {
      const v = q(a + 0.5, b + 0.5);
      if (v >= 0.68 && v < 0.86) box(a, b, 1, 1, 6, 0, crowdM([C('#7a3f9a'), C('#e8c032'), C('#f1ead8'), C('#d8302a')], C('#3a2a40')), (x, y) => (y & 1 ? cc : sh(cc, 0.9)), (x, y) => sh(cc, 0.7), { ns: 1 });
      else if (v >= 0.86 && v < 1.03) box(a, b, 1, 1, 10, 0, crowdM([C('#e8c032'), C('#7a3f9a'), C('#d8302a'), C('#f1ead8')], C('#3a2a40')), (x, y) => (y & 1 ? cc : sh(cc, 0.9)), (x, y) => sh(cc, 0.7), { ns: 1 });
    }
    for (let k = 0; k < 11; k++) person(ci - 4 + r() * 8, cj - 3.2 + r() * 6.4, k < 9 ? C('#f1ead8') : pick(r, PCOL), 0, 0.2);
    for (const [mi, mj] of [[27.8, 54.3], [44.2, 54.3], [27.8, 68.7], [44.2, 68.7]]) {
      box(mi - 0.1, mj - 0.1, 0.2, 0.2, 34, 0, C('#cfd6da'), C('#b0b8bd'), C('#808890'), { ns: 1 });
      box(mi - 0.6, mj - 0.15, 1.2, 0.3, 3, 34, C('#f6f0d0'), C('#d8d0b0'), C('#a8a088'), { ns: 1 });
      for (let k = 0; k < 5; k++) glow(mi - 0.5 + k * 0.25, mj + 0.2, 35, C('#fff6c0'));
    }
    // pagoda
    ground(25, 55, 4, 4, T.LAWN); gRect(25.2, 58, 3.6, 1, T.POND);
    for (let k = 0; k < 5; k++) {
      const w = 2.2 - k * 0.38, o = (2.2 - w) / 2;
      box(26 + o, 55.2 + o, w, w, 2, k * 4, WH, WH, sh(WH, 0.72), { ns: 1 });
      box(25.9 + o, 55.1 + o, w + 0.2, w + 0.2, 2, k * 4 + 2, C('#b23a34'), C('#a03a30'), C('#7a2a26'), { ns: 1 });
    }
    spire(27.1, 56.3, 20, 0.2, 7, GOLD);
    maidan(25, 49, 47, 71, r, { tp: 0.07 });
  }

  function r3c3(r) {
    const M = WH;
    ground(49, 49, 22, 22, T.LAWN);
    ground(59, 49, 2, 22, T.REDPATH); ground(49, 65.5, 22, 1, T.REDPATH);
    ground(49.6, 52.6, 4, 6.8, T.PLAZA); ground(50, 53, 3.2, 6, T.POND);
    ground(66.4, 52.6, 4, 6.8, T.PLAZA); ground(66.8, 53, 3.2, 6, T.POND);
    ground(57.5, 60.5, 5, 8.5, T.PLAZA); ground(58, 61, 4, 7, T.POND);
    const stone = [sh(M, 0.96), sh(M, 0.7)];
    B(54, 52, 12, 8, 3, M, { mats: stone, roof: roofM(C('#ece5d4')) });
    B(57, 60, 6, 0.7, 2, M, { mats: stone, roof: M });
    const mkw = () => wallM(M, { cw: 4, ww: 2, wh: 4, wy: 1, rh: 8, win: C('#7e8e9c'), litP: 3 });
    B(56, 54, 8, 4, 20, M, { z: 3, mats: pairM(() => wallM(M, { cw: 4, ww: 2, wh: 4, wy: 1, rh: 9, win: C('#7e8e9c'), litP: 3 })), roof: M, nc: 1 });
    const mkt = () => wallM(M, { cw: 4, ww: 2, wh: 3, rh: 8, win: C('#7e8e9c'), litP: 3 });
    for (const [i, j] of [[54, 52], [64, 52], [54, 58], [64, 58]]) {
      B(i, j, 2, 2, 24, M, { z: 3, mats: pairM(mkt), roof: M, nc: 1 });
      drum(i + 1, j + 1, 27, 0.8, 2, M, M); dome(i + 1, j + 1, 29, 0.85, 9, M, { rib: 3 }); line3([i + 1, j + 1, 38], [i + 1, j + 1, 42], GOLD, 0.3);
    }
    const colw = () => colM(M, { ch: 9, per: 4, dark: C('#7a766c'), win: C('#7e8e9c'), litP: 0 });
    B(56, 58, 8, 2, 12, M, { z: 3, mats: pairM(colw), roof: M, nc: 1 });
    B(56, 52, 8, 2, 12, M, { z: 3, mats: pairM(colw), roof: M, nc: 1 });
    B(58, 59.4, 4, 1.4, 15, M, { z: 3, mats: pairM(() => colM(M, { ch: 13, per: 3, dark: C('#6a665c') })), roof: M, nc: 1 });
    gable(58, 59.4, 4, 1.4, 4, 18, true, M);
    const dside = (a, t, hh) => (a % 5 === 2 && t >= 2 && t < hh - 2 ? C('#7e8e9c') : M);
    drum(60, 56, 23, 1.6, 10, M, dside);
    dome(60, 56, 33, 1.75, 22, M, { rib: 4 });
    box(59.75, 55.75, 0.5, 0.5, 5, 55, M, M, sh(M, 0.7), { ns: 1 });
    stamp(60, 56, 60, ['..b..', 'b.b.b', 'bbbbb', '..b..', '.b.b.'], { b: C('#4a3a28') }, 0.6);
    const fl = [C('#e2452f'), C('#f4c531'), C('#e48fb0'), C('#f2f0e0')];
    // lawn life
    claim(54, 52, 12, 9); claim(57, 60, 6, 9);
    for (let b = 49; b < 71; b++) for (let a = 49; a < 71; a++) if ((a < 51 || a > 68 || b < 51 || b > 68) && (a + b) % 2 === 0 && isFree(a, b, 1, 1)) { tree(a, b, [0, 7, 3, 6, 1, 5][(a * 5 + b) % 6], a * 9 + b); claim(a, b, 1, 1); }
    for (let k = 0; k < 14; k++) { const a = 51 + ri(r, 18), b = 62 + ri(r, 8); if (isFree(a, b, 1, 1)) { tree(a, b, pick(r, [0, 7, 3, 6]), k); claim(a, b, 1, 1); } }
    for (let k = 0; k < 7; k++) {
      const i = k < 4 ? 50.5 + r() * 6 : 63 + r() * 6, j = 62 + r() * 6;
      R(Math.round(sx(i, j)) - 2, Math.round(sy(i, j)) - 1, 5, 3, pick(r, PCOL), i + j + 0.05);
      for (let q = 0; q < 3; q++) person(i - 0.3 + q * 0.3, j - 0.2 + (q & 1) * 0.3, pick(r, PCOL));
    }
    { const i = 64.5, j = 64.3; person(i, j, C('#f1ead8')); const x = Math.round(sx(i, j)), y = Math.round(sy(i, j));
      for (let k = 0; k < 6; k++) { const bx = x - 4 + k * 2, by = y - 12 - (k % 3) * 2; LN(x, y - 2, bx, by + 2, C('#e9e2d0'), i + j + 1); R(bx - 1, by - 1, 2, 2, fl[k % 4], i + j + 1.05); } }
    for (const [i, j] of [[58.4, 63], [61.2, 63], [58.4, 69], [61.2, 69]]) { box(i, j, 0.4, 0.4, 3, 0, M, sh(M, 0.9), sh(M, 0.7), { ns: 1 }); pt(i + 0.2, j + 0.2, 5, C('#a89a80'), 0.4); pt(i + 0.2, j + 0.2, 4, C('#a89a80'), 0.4); }
    crowd(55, 60.6, 10, 2, 28, r, PCOL);
    for (let k = 0; k < 9; k++) glow(56.6 + k * 0.85, 60.0, 8, C('#ffdf80'));
    for (let k = 0; k < 6; k++) { glow(58.2 + k * 0.7, 60.75, 11, C('#ffdf80')); }
    for (let k = 0; k < 14; k++) { const a = k / 14 * Math.PI * 2; glow(60 + Math.cos(a) * 1.75, 56 + Math.sin(a) * 1.75, 31, C('#ffe9a8')); }
    for (const [i, j] of [[53.3, 61], [66.7, 61], [58, 70], [62, 70], [59.5, 51], [60.5, 51]]) lamp(i, j);
    vehicle('carriage', 56.5, 49.5, 0, 'i'); vehicle('carriage', 63, 49.6, 0, 'i');
  }

  function r3c4(r) {
    gRect(73, 49, 14, 22, T.GRASS);
    ground(74.6, 50.6, 3.8, 3.8, T.PLAZA);
    drum(76.5, 52.5, 0, 1.5, 6, WH, WH); dome(76.5, 52.5, 6, 1.5, 4, WH); line3([76.5, 52.5, 10], [76.5, 52.5, 16], GOLD, 0.2);
    B(77.4, 55, 5.6, 2, 10, WH, { cw: 4, ww: 1, wh: 4, win: C('#7a8a96'), litP: 0, band: C('#e0dac8') });
    gable(77.4, 55, 5.6, 2, 4, 10, false, C('#a8a090'));
    churchSpire(75.9, 55, 1.5, 1.5, 22, 14, WH, C('#cfd2d6'));
    ground(82, 60, 10, 8, T.PLAZA);
    B(82, 60, 4, 2.5, 10, C('#e8dcc0'), { cw: 5, win: C('#5a6a78'), band: C('#b9b4a8'), cornice: C('#b9b4a8'), litP: 3 });
    B(88, 60, 4, 3, 8, C('#b9b4a8'), { cw: 5, win: C('#4a5a68'), band: CREAM, litP: 3 });
    B(82, 66, 3, 2, 7, C('#cfc8b8'), { cw: 5, win: C('#4a5a68'), litP: 3 }); B(89, 65.5, 3, 2, 6, C('#e8dcc0'), { cw: 5, win: C('#4a5a68'), litP: 3 });
    crowd(83, 62.7, 8, 3.5, 60, r, PCOL);
    ground(75, 63, 6, 5, T.FIELD);
    for (const gx of [75.05, 80.95]) { line3([gx, 65, 0], [gx, 65, 3], WH, 0.2); line3([gx, 66, 0], [gx, 66, 3], WH, 0.2); line3([gx, 65, 3], [gx, 66, 3], WH, 0.2); }
    crowd(75.3, 63.3, 5.4, 4.4, 16, r, [C('#d8302a'), C('#2f66b0')]);
    B(73.2, 58.5, 1.8, 1.2, 4, C('#9fc9e4'), { mats: [C('#9fc9e4'), C('#7aa8c4')], roof: C('#2f6fb5') });
    fill(87, 49, 95, 71, 'park', r);
    maidan(73, 49, 87, 71, r, { tp: 0.08 });
  }

  function r3c5(r) {
    ground(98, 49, 9, 6, T.DARKGRASS);
    for (let k = 0; k < 16; k++) {
      const i = 98.5 + r() * 8, j = 49.5 + r() * 4.5, g = C(['#a8a8a0', '#bdb7ab', '#8e8e88'][k % 3]);
      if (k % 3 === 0) { stack(i, j, 0.4, 0.4, 10 + ri(r, 4), 0, (t) => 0.1 * t, sh(g, 1.1), g, sh(g, 0.7)); }
      else { box(i, j, 0.8, 0.8, 3, 0, g, sh(g, 1.05), sh(g, 0.72), { ns: 1 }); dome(i + 0.4, j + 0.4, 3, 0.45, 3, g); }
    }
    for (let b = 49; b < 55; b++) for (let a = 98; a < 107; a++) if ((a + b) % 3 === 0) { tree(a, b, (a + b) % 2 ? 5 : 1, a * 3 + b); }
    // roundabout
    const cx = 107.5, cy = 61.5;
    ground(97, 61, 20, 1, T.ROAD); ground(107, 49, 1, 22, T.ROAD);
    const spoke = (i, j) => { for (const a of [Math.PI / 4, 3 * Math.PI / 4, 5 * Math.PI / 4]) { const dx = i - cx, dy = j - cy, t = dx * Math.cos(a) + dy * Math.sin(a), p = Math.abs(-dx * Math.sin(a) + dy * Math.cos(a)); if (t > 1.8 && t < 4.3 && p < 0.5) return true; } return false; };
    groundFn(100, 54, 115, 69, (i, j) => { const d = Math.hypot(i - cx, j - cy); return d < 1.4 ? T.LAWN : d < 2.4 ? T.ROAD : spoke(i, j) ? T.ROAD : 0; });
    tree(107, 61, 1, 3); tree(106, 60, 3, 4);
    // mosque
    B(99.5, 56.2, 4.5, 3.8, 8, WH, { cw: 4, ww: 1, wh: 4, win: C('#3f8f6a'), band: C('#e0dac8'), litP: 3 });
    drum(101.75, 58.1, 8, 1.2, 2, C('#e0dac8'), C('#e0dac8')); dome(101.75, 58.1, 10, 1.3, 8, C('#2f8f5a'), { rib: 3 });
    minaret(99.5, 59.2, 28, WH, C('#2f8f5a')); minaret(103.2, 59.2, 28, WH, C('#2f8f5a'));
    // biryani lane
    [101, 104.1, 108.3, 111.3].forEach((ci, k) => {
      const aw = [C('#d8302a'), C('#f1ead8')], base = C(['#f1e6c8', '#e8c468', '#e6b8a8', '#d9c3a0'][k]);
      B(ci, 64.6, 2.7, 3, 11, base, { cw: 4, win: C('#2f5f4a'), band: sh(base, 0.84), shop: [aw[0], aw[1], C('#3a2418')], litP: 2 });
      for (const o of [0.6, 1.8]) { const d = drum(ci + o, 68.3, 0, 0.28, 4, C('#e8a060'), C('#c8763a')); R(Math.round(sx(ci + o, 68.3)) - 2, Math.round(sy(ci + o, 68.3, 4)) - 1, 4, 1, C('#8a3a1a'), ci + o + 68.3 + 0.3); }
    });
    B(110, 51, 3, 4, 9, CREAM, { cw: 4, ww: 1, wh: 4, win: C('#6a7a86'), litP: 0 });
    gable(110, 51, 3, 4, 4, 9, true, C('#a8503a'));
    churchSpire(110.8, 50.1, 1.2, 1.2, 14, 10, CREAM, C('#8a8f9a'));
    stalls(97, 49, 117, 71, r, { p: 0.1, rs: 3 });
    fill(97, 49, 117, 71, 'south', r);
    fill(119, 49, 120, 96, 'south', r, { nolanes: true });
  }

  function r4c1(r) {
    ground(13, 75, 9, 6, T.LAWN);
    groundFn(10, 73, 16, 96, (i, j) => (i > L.eb(j) + 0.1 && i < L.eb(j) + 1.6 ? T.PLAZA : 0));
    groundFn(9, 78, 14, 83, (i, j) => (i > L.eb(j) - 1.2 && i < L.eb(j) + 1.0 ? T.STEPS : 0));
    ground(20.5, 73, 1, 10, T.RAILJ); claim(20, 73, 2, 10);
    B(14, 76, 4, 2.5, 9, WH, { mats: pairM(() => colM(WH, { ch: 8, per: 4, dark: C('#7f7b70'), cornice: WH })), roof: WH });
    box(13.7, 78.5, 4.6, 0.6, 1, 0, WH, WH, sh(WH, 0.72), { ns: 1 });
    for (let k = 0; k < 4; k++) tree(13 + k * 2 | 0, 80, 3 + (k & 1) * 3, k);
    for (const [i, j] of [[19.5, 76], [19.5, 79]]) tree(i | 0, j, 0, j);
    for (let j = 74; j < 84; j += 3) lamp(L.eb(j) + 1.3, j);
    for (const [i, j] of [[9.4, 79], [8.4, 82.5], [9.8, 90], [8.2, 93]]) vehicle('boat', i, j, 0, 'j');
    crowd(11.5, 74, 3, 9, 14, r, PCOL);
    claim(0, 84, 20, 2);
    fill(12, 73, 23, 84, 'south', r, { treeP: 0.2 });
    fill(12, 87, 23, 96, 'south', r, { treeP: 0.25 });
  }

  function r4c2(r) {
    groundFn(27, 73, 28, 96, (i, j) => (j < 84 || j >= 86 ? T.POND : 0));
    for (const j of [79.5, 91.2]) { box(26.5, j, 2.0, 0.8, 1, 0, WOOD, C('#8a6a43'), C('#6a4a32'), { ns: 1 }); for (const q of [26.5, 28.3]) pt(q, j + 0.8, 2, C('#6a4a32'), 0.3), pt(q, j, 2, C('#6a4a32'), 0.3); }
    ground(32, 75, 8, 8, T.PLAZA);
    const GRY = C('#bdb7ab'), GRN = C('#2f8f5a'), RED = C('#d8302a'), BLU = C('#2f6fb5');
    const tem = (a, t, h) => { const fb = h - 1 - t; if (a > 20 && a < 28 && fb > 0 && fb < 6) return C('#2a1a14'); return fb === 0 ? GRY : fb === 3 ? GRN : fb === 5 ? RED : fb === 7 ? BLU : fb === 9 ? GRN : WH; };
    B(33.8, 76.8, 3.4, 3.4, 11, WH, { mats: [tem, shadeM(tem, 0.74)], roof: WH });
    const cf = (t) => 0.26 * (1 - (1 - t) * (1 - t));
    stack(33.4, 76.4, 4.2, 4.2, 8, 11, cf, C('#eceef2'), C('#c8ccd4'), C('#9aa0ad'));
    stack(34.4, 77.4, 2.2, 2.2, 8, 19, cf, C('#eceef2'), C('#c8ccd4'), C('#9aa0ad'));
    spire(35.5, 78.5, 27, 0.35, 10, GOLD);
    B(33.5, 80.6, 4, 1.6, 5, WH, { mats: pairM(() => colM(WH, { ch: 4, per: 4, dark: C('#6a665c') })), roof: sh(WH, 0.9) });
    for (let k = 0; k < 32; k++) person(36.8 + Math.sin(k / 3) * 0.25, 82.6 + k * 0.33, pick(r, [C('#f1ead8'), C('#d8452f'), C('#e8c032'), C('#f08a24')]), 0, 0.5);
    for (const [i, j] of [[32.5, 79.2], [38.6, 78.6], [33.1, 82.6], [38.2, 82]]) mound(i, j, [C('#e2242f'), C('#c8182a'), C('#f04a3a')]);
    for (const [i, j] of [[33, 76], [38.5, 76.2], [35.5, 82.8]]) { ring(i, j, 0.7, WH, 28); ring(i, j, 0.4, C('#f6c0c0'), 16); }
    for (const [i, j] of [[32, 83], [39, 83], [32, 75], [39, 75]]) if (isFree(i, j, 1, 1)) smallStall(i, j, r);
    crowd(32.5, 75.5, 7, 7, 30, r, PCOL);
    stalls(25, 73, 47, 96, r, { p: 0.12, rs: 3 });
    fill(25, 86, 47, 96, 'south', r);
    fill(25, 73, 47, 86, 'north', r);
  }

  function r4c3(r) {
    gRect(49, 73, 22, 23, T.GRASS);
    gFn(49, 73, 71, 96, (i, j) => (L.inLake(i, j) ? T.POND : 0));
    claimFn(49, 73, 71, 96, (i, j) => { for (const [a, b] of [[0, 0], [-0.25, -0.25], [0.25, 0.25], [-0.25, 0.25], [0.25, -0.25]]) if (L.inLake(i + a, j + b)) return true; return false; });
    const near = (i, j) => { for (let k = 0; k < 8; k++) { const a = k * Math.PI / 4; if (L.inLake(i + 0.6 * Math.cos(a), j + 0.6 * Math.sin(a))) return true; } return false; };
    groundFn(49, 76, 71, 95, (i, j) => (!L.inLake(i, j) && near(i, j) ? T.REDPATH : 0));
    gDisc(60, 86, 2.3, 1.7, T.GRASS);
    for (const [i, j, k] of [[58, 85, 0], [61, 86, 1], [62, 84, 7], [58, 87, 3]]) tree(i, j, k, i + j);
    B(59.6, 85.2, 1.4, 1.0, 5, WH, { mats: [WH, sh(WH, 0.72)], roof: WH, nc: 1 }); dome(60.3, 85.7, 5, 0.5, 4, WH);
    box(59.8, 80.2, 0.4, 4.5, 1, 0, WOOD, C('#8a6a43'), C('#6a4a32'), { ns: 1 });
    B(56.3, 77.2, 3, 2.4, 6, CREAM, { cw: 4, win: C('#6a4a38'), band: sh(CREAM, 0.85), litP: 2, roof: C('#b23a34') });
    box(58.2, 79.6, 0.6, 2.6, 1, 0, WOOD, C('#8a6a43'), C('#6a4a32'), { ns: 1 });
    vehicle('shell', 57.2, 82.4, 0, 'j'); vehicle('shell', 59.2, 82.9, 0, 'j');
    for (let k = 0; k < 7; k++) { const i = 51 + (k % 4) * 1.1, j = 91 + ((k / 4) | 0) * 1.3; R(Math.round(sx(i, j)) - 2, Math.round(sy(i, j)) - 1, 4, 2, [C('#d8302a'), C('#2f66b0'), C('#e8c032'), C('#8a3f8f')][k % 4], i + j + 0.05); person(i, j - 0.15, pick(r, PCOL), 0, 0.3); }
    let i = 49; while (i < 70) { const w = 2 + ri(r, 2); if (i + w <= 71 && isFree(i, 73, w, 2)) building(i, 73, w, 2, STY.south, r, { shopP: 0.8 }); i += w; }
    maidan(49, 75, 71, 96, r, { tp: 0.3 });
    for (let k = 0; k < 8; k++) person(52 + r() * 16, 78 + r() * 3, pick(r, PCOL), 0, 0.3);
  }

  function r4c4(r) {
    ground(86, 86, 8, 9, T.RAILI);
    vehicle('tram', 89, 87.5, 0, 'i'); vehicle('tram', 90, 89.5, 0, 'i'); vehicle('tram', 89, 91.5, 0, 'i');
    B(86, 92.2, 8, 2.8, 5, C('#c9b9a0'), { roof: null, cw: 6, win: C('#4a3a30'), litP: 0 });
    gable(86, 92.2, 8, 2.8, 4, 5, false, C('#8f9aa0'));
    stalls(73, 73, 95, 96, r, { p: 0.3, rs: 2 });
    crowd(73, 73, 22, 23, 90, r, PCOL);
    fill(73, 73, 95, 96, 'garia', r);
  }

  function r4c5(r) {
    ground(99, 75, 12, 13, T.LAWN);
    ground(100.5, 77, 7, 7, T.PLAZA);
    drum(104, 80, 0, 2, 5, C('#e8eef2'), C('#e8eef2')); dome(104, 80, 5, 2, 12, C('#cfe3f2'), { rib: 5 });
    const st = (a) => ((a >> 1) & 1 ? C('#f1ead8') : C('#2f8f9a'));
    drum(101.5, 85, 0, 1.4, 9, C('#f1ead8'), (a, t, h) => st(a));
    for (let k = 0; k < 8; k++) { const tt = k / 7, i = 104 + k * 0.9, j = 84 + Math.sin(tt * Math.PI) * -1.2 + 1.2; B(i, j, 1, 1.6, 5, C('#e8eef2'), { mats: [C('#e8eef2'), C('#b9c7d0')], roof: C('#cfe3f2') }); }
    stamp(108, 78, 0, ['..ggg.', '.gggg.', 'ggggg.', 'g.gg..', '..gggg', '.gg..g'], { g: C('#3f9a4a') }, 0.4);
    const top = 24;
    for (const [i, j] of [[99.5, 87.3], [105, 81.6], [110.3, 76.2]]) box(i - 0.1, j - 0.1, 0.2, 0.2, top, 0, STEEL, STEEL, STEELD, { ns: 1 });
    line3([99.5, 87.3, top], [105, 81.6, top - 2], C('#2a2a30'), 0.2); line3([105, 81.6, top - 2], [110.3, 76.2, top], C('#2a2a30'), 0.2);
    for (const [i, j, c] of [[102.3, 84.4, '#d8302a'], [107.6, 78.9, '#f4c531']]) { line3([i, j, top - 1], [i, j, top - 5], C('#2a2a30'), 0.2); box(i - 0.2, j - 0.2, 0.4, 0.4, 3, top - 9, C(c), sh(C(c), 0.9), sh(C(c), 0.7), { ns: 1 }); }
    fill(111, 75, 115, 85, 'modern', r, { nolanes: true });
    // wetlands
    gRect(97, 88, 19, 8, T.GRASS); claim(97, 88, 20, 8);
    for (let a = 0; a < 4; a++) for (let b = 0; b < 2; b++) {
      const pi = 97.5 + a * 4.75, pj = 88.5 + b * 4;
      gRect(pi - 0.25, pj - 0.25, 4.25, 3.5, T.MARSH); gRect(pi, pj, 3.75, 3, T.POND);
    }
    for (const [i, j] of [[101, 89], [101, 93], [106, 90], [106, 94], [111, 89], [111, 93]]) tree(i, j, 2, i + j);
    person(101.8, 90.5, C('#f1ead8'), 0, 0.5); LN(Math.round(sx(101.8, 90.5)), Math.round(sy(101.8, 90.5)) - 2, Math.round(sx(103, 91)), Math.round(sy(103, 91)) - 1, C('#e9e2d0'), 193);
    person(106.7, 93.2, C('#d8452f'), 0, 0.5);
    vehicle('boat', 104, 90, 0, 'i'); vehicle('boat', 99.5, 93.8, 0, 'i');
    fill(97, 73, 117, 88, 'south', r);
    fill(119, 73, 120, 96, 'south', r, { nolanes: true });
  }

  const STEPS = [
    ['Laying tram tracks', baseGround],
    ['Raising the Howrah Bridge', structures],
    ['Moulding clay idols in Kumartuli', r1c1],
    ['Dusting off Thakur Bari', r1c2],
    ['Stacking books on College Street', r1c3],
    ['Shunting trains into Sealdah', r1c4],
    ['Pitching the Bagbazar pandal', r1c5],
    ['Whistling into Howrah Station', r2c1],
    ['Stringing marigolds at Mullick Ghat', r2c2],
    ["Inking ledgers at Writers' Building", r2c3],
    ['Haggling at New Market', r2c4],
    ['Hanging fairy lights on Park Street', r2c5],
    ['Marching around Fort William', r3c1],
    ['Bowling at Eden Gardens', r3c2],
    ['Polishing Victoria Memorial', r3c3],
    ['Painting the Planetarium dome', r3c4],
    ['Simmering biryani at Park Circus', r3c5],
    ['Sweeping Prinsep Ghat', r4c1],
    ['Queueing at Kalighat', r4c2],
    ['Rowing on Rabindra Sarobar', r4c3],
    ['Bargaining at Gariahat', r4c4],
    ['Launching Science City', r4c5],
    ['Laying the earth beneath', slab],
  ];

  function reset() { E.col.fill(0); E.dep.fill(-1e9); E.G.fill(0); E.SHD.fill(0); OCC.fill(0); RD.fill(0); E.lights.length = 0; }
  const runStep = (k) => STEPS[k][1](E.rng(9000 + k * 131));

  function build() {
    reset();
    E.S.dry = true;
    try { for (let k = 0; k < STEPS.length; k++) runStep(k); } finally { E.S.dry = false; }
    E.renderGround();
    OCC.fill(0);
    for (let k = 0; k < STEPS.length; k++) runStep(k);
    return PK.city;
  }
  function buildAsync(onProgress) {
    return new Promise((resolve, reject) => {
      reset();
      let pass = 0, k = 0;
      const N = STEPS.length;
      E.S.dry = true;
      const tick = () => {
        try {
          if (k < N) {
            runStep(k);
            if (onProgress) onProgress((pass * N + k + 1) / (2 * N), STEPS[k][0]);
            k++; setTimeout(tick, 0);
          } else if (pass === 0) {
            E.S.dry = false; E.renderGround(); OCC.fill(0); pass = 1; k = 0; setTimeout(tick, 0);
          } else resolve(PK.city);
        } catch (e) { E.S.dry = false; reject(e); }
      };
      setTimeout(tick, 0);
    });
  }

  PK.city = { build, buildAsync, fill, steps: STEPS.map((s) => s[0]) };
  if (typeof module !== 'undefined') module.exports = PK;
})(typeof window !== 'undefined' ? window : globalThis);



