(function () {
  'use strict';

  /* feature table */

  var FEATS = ['vowel','consonantal','sonorant','continuant','stop','fricative','affricate','nasal','approximant','rhotic','lateral','voice','labial','dental','alveolar','retroflex','palatal','velar','uvular','glottal','high','low','front','back','round','tense','stressed','long','aspirated','ejective'];
  var ALIAS = { syll:'vowel', syllabic:'vowel', cons:'consonantal', son:'sonorant', cont:'continuant', voiced:'voice', stress:'stressed', approx:'approximant', plosive:'stop', fric:'fricative', affr:'affricate', lat:'lateral', lab:'labial', alv:'alveolar', pal:'palatal', vel:'velar', uv:'uvular', glot:'glottal', ret:'retroflex', dent:'dental', asp:'aspirated', ej:'ejective' };
  var PLACE = ['labial','dental','alveolar','retroflex','palatal','velar','uvular','glottal'];
  var MANNER = ['stop','fricative','affricate','nasal','approximant','rhotic'];
  var MODF = ['long','aspirated','ejective','stressed'];
  var TAB = [], TABMAP = {};

  function blank() { var f = {}; FEATS.forEach(function (k) { f[k] = false; }); return f; }
  function derive(f) {
    f.sonorant = !!(f.vowel || f.nasal || f.approximant || f.rhotic);
    f.continuant = !!(f.vowel || f.fricative || f.approximant);
  }
  function add(sym, f) { derive(f); TAB.push({ sym: sym, f: f }); if (!TABMAP[sym]) TABMAP[sym] = TAB[TAB.length - 1]; }

  var PL = { b:'labial', d:'dental', a:'alveolar', r:'retroflex', p:'palatal', v:'velar', u:'uvular', g:'glottal' };
  var MN = { s:['stop'], f:['fricative'], F:['fricative','lateral'], a:['affricate'], n:['nasal'], l:['approximant','lateral'], r:['rhotic'], j:['approximant'] };
  ('p:sb0 b:sb1 t:sa0 d:sa1 ʈ:sr0 ɖ:sr1 c:sp0 ɟ:sp1 k:sv0 g:sv1 q:su0 ɢ:su1 ʔ:sg0 ɸ:fb0 β:fb1 f:fb0 v:fb1 θ:fd0 ð:fd1 s:fa0 z:fa1 ʃ:fp0 ʒ:fp1 ɕ:fp0 ʑ:fp1 ç:fp0 ʝ:fp1 x:fv0 ɣ:fv1 χ:fu0 ʁ:fu1 h:fg0 ɦ:fg1 ɬ:Fa0 ɮ:Fa1 ts:aa0 dz:aa1 tʃ:ap0 dʒ:ap1 tɕ:ap0 dʑ:ap1 m:nb1 n:na1 ɳ:nr1 ɲ:np1 ŋ:nv1 ɴ:nu1 l:la1 ɭ:lr1 ʎ:lp1 r:ra1 ɾ:ra1 ɹ:ja1 j:jp1 w:jb1 ɥ:jp1 ʋ:jb1 ɰ:jv1').split(' ').forEach(function (it) {
    var p = it.split(':'), c = p[1], f = blank();
    f.consonantal = c[0] !== 'j'; f.voice = c[2] === '1'; f[PL[c[1]]] = true;
    MN[c[0]].forEach(function (x) { f[x] = true; });
    add(p[0], f);
  });
  var LAX = 'ɪʏʊɛœɔʌɜɞɐæəɚ';
  ('ihf0 yhf1 ɨhc0 ʉhc1 ɯhb0 uhb1 ɪhf0 ʏhf1 ʊhb1 emf0 ømf1 ɘmc0 ɵmc1 ɤmb0 omb1 əmc0 ɚmc0 ɛmf0 œmf1 ɜmc0 ɞmc1 ʌmb0 ɔmb1 ælf0 ɐlc0 alf0 ɶlf1 ɑlb0 ɒlb1').split(' ').forEach(function (it) {
    var f = blank();
    f.vowel = true; f.voice = true; f.high = it[1] === 'h'; f.low = it[1] === 'l';
    f.front = it[2] === 'f'; f.back = it[2] === 'b'; f.round = it[3] === '1';
    f.tense = LAX.indexOf(it[0]) < 0; if (it[0] === 'ɚ') f.rhotic = true;
    add(it[0], f);
  });
  var DIG = { ts:1, dz:1, 'tʃ':1, 'dʒ':1, 'tɕ':1, 'dʑ':1 };

  function setF(f, n, v) {
    f[n] = v;
    if (v) {
      if (PLACE.indexOf(n) >= 0) PLACE.forEach(function (p) { if (p !== n) f[p] = false; });
      if (MANNER.indexOf(n) >= 0) MANNER.forEach(function (p) { if (p !== n) f[p] = false; });
      if (n === 'high') f.low = false; if (n === 'low') f.high = false;
      if (n === 'front') f.back = false; if (n === 'back') f.front = false;
    }
  }

  /* segmenting IPA */

  var COMB = /[\u0300-\u036f]/, MODL = 'ʰʷʲˠˤʼːˑ˔', BT = { '#':'#', '+':'+', '$':'.' };
  var UNK = {};
  function keyOf(s) { return s.replace(/[\u035c\u0361]/g, ''); }

  function nextSeg(s, i) {
    var j = i, cp = String.fromCodePoint(s.codePointAt(j));
    j += cp.length;
    if (DIG[cp + (s[j] || '')]) j += 1;
    while (j < s.length) {
      var c = s[j];
      if (c === '\u0361' || c === '\u035c') {
        j++;
        if (j < s.length) j += String.fromCodePoint(s.codePointAt(j)).length;
      } else if (COMB.test(c) || MODL.indexOf(c) >= 0) j++;
      else break;
    }
    return [s.slice(i, j), j];
  }

  function segFromToken(t) {
    var tie = false, mods = [], bc = [], f, e;
    Array.from(t).forEach(function (c) {
      if (c === '\u0361' || c === '\u035c') tie = true;
      else if (COMB.test(c) || MODL.indexOf(c) >= 0) mods.push(c);
      else bc.push(c);
    });
    e = TABMAP[bc.join('')];
    if (e) f = Object.assign({}, e.f);
    else if (bc.length > 1 && TABMAP[bc[0]]) {
      f = Object.assign({}, TABMAP[bc[0]].f);
      var e2 = TABMAP[bc[bc.length - 1]];
      f.stop = false; f.affricate = true;
      if (e2) PLACE.forEach(function (p) { f[p] = e2.f[p]; });
    } else { f = blank(); UNK[t] = true; }
    mods.forEach(function (m) {
      if (m === '\u0303') f.nasal = true;
      else if (m === 'ː') f.long = true;
      else if (m === 'ʰ') f.aspirated = true;
      else if (m === 'ʼ') f.ejective = true;
      else if (m === '\u0325') f.voice = false;
      else if (m === '\u032c') f.voice = true;
      else if (m === '\u032a') { f.dental = true; f.alveolar = false; }
    });
    derive(f);
    return { type: 'seg', sym: t, key: keyOf(t), f: f };
  }

  /* feature bundle -> IPA symbol */
  function lookup(f) {
    function dist(e, flip) {
      var d = 0;
      FEATS.forEach(function (k) {
        if (MODF.indexOf(k) >= 0 || (k === 'nasal' && f.vowel)) return;
        var v = e.f[k]; if (flip && k === 'voice') v = !v;
        if (!!v !== !!f[k]) d++;
      });
      return d;
    }
    var best = null, bd = 99, b2 = null, d2 = 99, i, d, out, approx = false;
    for (i = 0; i < TAB.length; i++) { d = dist(TAB[i], false); if (d < bd) { bd = d; best = TAB[i]; } }
    if (bd === 0) out = best.sym;
    else {
      for (i = 0; i < TAB.length; i++) { d = dist(TAB[i], true); if (d < d2) { d2 = d; b2 = TAB[i]; } }
      if (d2 === 0) out = b2.sym + (f.voice ? '\u032c' : '\u0325');
      else { out = best.sym; approx = true; }
    }
    if (f.vowel && f.nasal) out += '\u0303';
    if (f.long) out += 'ː'; if (f.aspirated) out += 'ʰ'; if (f.ejective) out += 'ʼ';
    return { sym: out, approx: approx };
  }

  /* words */

  function bnd(c) { return { type: c === '$' ? '.' : c, sym: c === '$' ? '.' : c, key: c === '$' ? '.' : c }; }

  function parseWord(w, dots) {
    var s = w.replace(/[\[\]\/]/g, ''), arr = [bnd('#')], i = 0, mk = null, pend = false;
    while (i < s.length) {
      var c = s[i];
      if (c === 'ˈ' || c === 'ˌ') { mk = c; pend = c === 'ˈ'; i++; continue; }
      if (c === '.') { if (!dots) arr.push(bnd('$')); i++; continue; }
      if (c === '+' || c === '-') { arr.push(bnd('+')); i++; continue; }
      if (/\s/.test(c)) { i++; continue; }
      var r = nextSeg(s, i), sg = segFromToken(r[0]);
      i = r[1];
      if (mk) { sg.mk = mk; mk = null; }
      if (pend && sg.f.vowel) { sg.f.stressed = true; pend = false; }
      arr.push(sg);
    }
    arr.push(bnd('#'));
    return arr;
  }

  function str(arr, final) {
    return arr.map(function (g) {
      if (g.type === '#') return '';
      if (g.type === '+') return final ? '' : '+';
      return (g.mk || '') + g.sym;
    }).join('');
  }

  /* rule parser */

  function pMat(s) {
    return s.split(/[\s,]+/).filter(Boolean).map(function (tok) {
      var m = /^([+\-\u2212]?)([αβγδ]?)([a-z]+)$/i.exec(tok);
      if (!m || (!m[1] && !m[2])) throw new Error('feature "' + tok + '" needs + or - in front');
      var n = m[3].toLowerCase(); n = ALIAS[n] || n;
      if (FEATS.indexOf(n) < 0) throw new Error('unknown feature "' + m[3] + '"');
      return { n: n, pos: m[1] === '' || m[1] === '+', a: m[2] || null };
    });
  }

  function pSeq(P, close) {
    var out = [], s = P.s;
    while (P.i < s.length) {
      var c = s[P.i], el;
      if (close && (c === close || (close === '}' && c === ','))) break;
      if (/\s/.test(c)) { P.i++; continue; }
      if (c === ')' || c === '}' || c === ']') throw new Error('unexpected "' + c + '"');
      if (c === '[') {
        var j = s.indexOf(']', P.i);
        if (j < 0) throw new Error('missing "]"');
        el = { t: 'mat', specs: pMat(s.slice(P.i + 1, j)) }; P.i = j + 1;
      } else if (c === '(') {
        P.i++; var inner = pSeq(P, ')');
        if (s[P.i] !== ')') throw new Error('missing ")"');
        P.i++; el = { t: 'opt', seq: inner };
      } else if (c === '{') {
        P.i++; var alts = [];
        for (;;) { alts.push(pSeq(P, '}')); if (s[P.i] === ',') { P.i++; continue; } break; }
        if (s[P.i] !== '}') throw new Error('missing "}"');
        P.i++; el = { t: 'alt', alts: alts };
      } else if (c === '#' || c === '+' || c === '$') { el = { t: 'bnd', v: c }; P.i++; }
      else if (c === '∅' || c === 'Ø') { P.i++; continue; }
      else if (/[A-Z]/.test(c)) { el = { t: 'cls', v: c }; P.i++; }
      else { var r = nextSeg(s, P.i); el = { t: 'sym', seg: r[0], key: keyOf(r[0]) }; P.i = r[1]; }
      if (s[P.i] === '*') { el = { t: 'star', seq: [el] }; P.i++; }
      out.push(el);
    }
    return out;
  }

  function pSlot(s) {
    var t = s.trim();
    if (/^(0|∅|Ø)?$/.test(t)) return [];
    var P = { s: t, i: 0 };
    return pSeq(P, null);
  }

  function parseRule(line) {
    var mode = null, m = /\s@(ltr|rtl|sim)\s*$/.exec(line);
    if (m) { mode = m[1]; line = line.slice(0, m.index); }
    line = line.replace('→', '>');
    var g = line.indexOf('>');
    if (g < 0) throw new Error('needs ">", like t > d / V _ V');
    var rest = line.slice(g + 1), sl = rest.indexOf('/');
    var env = sl < 0 ? '_' : rest.slice(sl + 1), u = env.indexOf('_');
    if (u < 0) throw new Error('context needs "_" for the target position');
    return { T: pSlot(line.slice(0, g)), X: pSlot(sl < 0 ? rest : rest.slice(0, sl)),
             L: pSlot(env.slice(0, u)), R: pSlot(env.slice(u + 1)), mode: mode };
  }

  function compile(text) {
    var rules = [], errors = [], classes = {
      C: { specs: [{ n: 'vowel', pos: false }] }, V: { specs: [{ n: 'vowel', pos: true }] }
    };
    text.split(/\r?\n/).forEach(function (raw, idx) {
      var line = raw.trim();
      if (!line || line.indexOf('//') === 0) return;
      try {
        var cm = /^([A-Z])\s*=\s*(.+)$/.exec(line);
        if (cm) {
          var body = cm[2].trim();
          if (body[0] === '[') classes[cm[1]] = { specs: pMat(body.replace(/^\[|\]$/g, '')) };
          else {
            var keys = [], j = 0, b = body.replace(/[\/,\s]+/g, '');
            while (j < b.length) { var r = nextSeg(b, j); keys.push(keyOf(r[0])); j = r[1]; }
            classes[cm[1]] = { keys: keys };
          }
          return;
        }
        rules.push(parseRule(line));
      } catch (e) { errors.push('Line ' + (idx + 1) + ': ' + e.message); }
    });
    return { rules: rules, classes: classes, errors: errors };
  }

  /* matcher (backtracking, continuation style) */

  function matchSpecs(specs, seg, env) {
    if (seg.type !== 'seg') return null;
    var e = env;
    for (var i = 0; i < specs.length; i++) {
      var s = specs[i], v = !!seg.f[s.n];
      if (s.a) {
        if (e[s.a] === undefined) { if (e === env) e = Object.assign({}, env); e[s.a] = s.pos ? v : !v; }
        else if (v !== (s.pos ? e[s.a] : !e[s.a])) return null;
      } else if (v !== s.pos) return null;
    }
    return e;
  }

  function one(el, seg, env, C) {
    if (!seg) return null;
    if (el.t === 'bnd') return seg.type === BT[el.v] ? env : null;
    if (el.t === 'sym') return seg.type === 'seg' && seg.key === el.key ? env : null;
    if (el.t === 'mat') return matchSpecs(el.specs, seg, env);
    var c = C.classes[el.v];
    if (!c) return null;
    if (c.specs) return matchSpecs(c.specs, seg, env);
    return seg.type === 'seg' && c.keys.indexOf(seg.key) >= 0 ? env : null;
  }

  function runSeq(seq, p, s, env, k, C) { return run(s > 0 ? seq : seq.slice().reverse(), 0, p, s, env, k, C); }

  function run(es, i, p, s, env, k, C) {
    if (i >= es.length) return k(p, env);
    var el = es[i];
    function next(p2, e2) { return run(es, i + 1, p2, s, e2, k, C); }
    if (el.t === 'opt') return runSeq(el.seq, p, s, env, next, C) || next(p, env);
    if (el.t === 'alt') {
      for (var a = 0; a < el.alts.length; a++) if (runSeq(el.alts[a], p, s, env, next, C)) return true;
      return false;
    }
    if (el.t === 'star') {
      return runSeq(el.seq, p, s, env, function (p2, e2) { return p2 !== p && run(es, i, p2, s, e2, k, C); }, C) || next(p, env);
    }
    var r = one(el, C.arr[p], env, C);
    return r ? next(p + s, r) : false;
  }

  function findAt(rule, arr, i, classes) {
    var res = null, C = { arr: arr, classes: classes };
    var ok = runSeq(rule.L, i - 1, -1, {}, function (pl, e1) {
      return run(rule.T, 0, i, 1, e1, function (e, e2) {
        return run(rule.R, 0, e, 1, e2, function (pr, e3) { res = { end: e, env: e3 }; return true; }, C);
      }, C);
    }, C);
    return ok ? res : null;
  }

  /* applying changes */

  function setSpecs(src, specs, env, notes) {
    var g = Object.assign({}, src), f = Object.assign({}, src.f), before = JSON.stringify(f);
    specs.forEach(function (s) {
      var v = s.pos;
      if (s.a && env[s.a] !== undefined) v = s.pos ? env[s.a] : !env[s.a];
      setF(f, s.n, v);
    });
    derive(f);
    if (JSON.stringify(f) !== before) {
      g.f = f;
      var r = lookup(f);
      g.sym = r.sym; g.key = keyOf(r.sym);
      if (r.approx) notes.approx = true;
    }
    return g;
  }

  function build(rule, old, env, notes) {
    var out = [];
    rule.X.forEach(function (el, j) {
      var src = old[Math.min(j, old.length - 1)];
      if (el.t === 'sym') {
        var ns = segFromToken(el.seg);
        if (src && src.type === 'seg') {
          if (src.f.vowel && ns.f.vowel) ns.f.stressed = src.f.stressed;
          if (j === 0 && src.mk) ns.mk = src.mk;
        }
        out.push(ns);
      } else if (el.t === 'mat') {
        if (src && src.type === 'seg') out.push(setSpecs(src, el.specs, env, notes));
        else notes.msgs['nothing'] = 'A rule tries to change features of nothing (an insertion). Write the new sound as a symbol, like ∅ > ə.';
      } else if (el.t === 'bnd') out.push(bnd(el.v));
    });
    return out;
  }

  function splice(arr, start, len, ins) {
    var carry = null, k;
    for (k = 0; k < len; k++) if (arr[start + k].mk && !carry) carry = arr[start + k].mk;
    if (carry) {
      var t = ins.length ? ins[0] : arr[start + len];
      if (t && t.type === 'seg' && !t.mk) t.mk = carry;
    }
    Array.prototype.splice.apply(arr, [start, len].concat(ins));
  }

  function applyRule(rule, arr, mode, classes, notes) {
    var ins = rule.T.length === 0, i, res, old, nw, guard = 0;
    mode = rule.mode || mode;
    if (mode === 'sim') {
      var ms = [], last = 0, hi = arr.length - 2 + (ins ? 1 : 0);
      for (i = 1; i <= hi; i++) {
        if (!ins && i < last) continue;
        res = findAt(rule, arr, i, classes);
        if (res) { ms.push({ i: i, end: res.end, env: res.env }); last = res.end; }
      }
      for (var q = ms.length - 1; q >= 0; q--) {
        var m = ms[q];
        splice(arr, m.i, m.end - m.i, build(rule, arr.slice(m.i, m.end), m.env, notes));
      }
    } else if (mode === 'ltr') {
      i = 1;
      while (i <= arr.length - 2 + (ins ? 1 : 0) && guard++ < 5000) {
        res = findAt(rule, arr, i, classes);
        if (!res) { i++; continue; }
        old = arr.slice(i, res.end); nw = build(rule, old, res.env, notes);
        splice(arr, i, old.length, nw);
        i += ins ? nw.length + 1 : nw.length;
        if (!nw.length && !old.length) i++;
      }
    } else {
      for (i = arr.length - 2 + (ins ? 1 : 0); i >= 1; i--) {
        res = findAt(rule, arr, i, classes);
        if (!res) continue;
        old = arr.slice(i, res.end);
        splice(arr, i, old.length, build(rule, old, res.env, notes));
      }
    }
  }

  function derivation(words, model, mode, dots) {
    var notes = { approx: false, msgs: {} };
    UNK = {};
    var rows = words.map(function (w) {
      var arr = parseWord(w, dots), prev = str(arr, false), cells = [];
      model.rules.forEach(function (r) {
        try { applyRule(r, arr, mode, model.classes, notes); } catch (e) { notes.msgs['err'] = 'Something went wrong: ' + e.message; }
        var cur = str(arr, false);
        cells.push(cur !== prev ? cur : null); prev = cur;
      });
      return { input: w, cells: cells, out: str(arr, true) };
    });
    return { rows: rows, notes: notes };
  }

  /* page */

  var PRESETS = [
    { label: 'Flapping (English)', m: 'sim',
      w: 'ˈbʌtɚ\nˈlædɚ\nˈætəm\nəˈtæk\nˈtɛn',
      r: '// t, d become a flap between a stressed and an unstressed vowel\n[+stop +cons +alveolar] > ɾ / [+vowel +stressed] _ [+vowel -stressed]' },
    { label: 'Plural (feeding, bleeding)', m: 'sim',
      w: 'kæt+z\nkæb+z\nbʌs+z\nbʊk+z\nwɪʃ+z',
      r: '// rule 1 inserts a vowel, which stops rule 2 from devoicing z\n∅ > ɪ / {s,z,ʃ,ʒ,tʃ,dʒ} + _ z\nz > s / [-voice] + _' },
    { label: 'Final devoicing (Russian)', m: 'sim',
      w: 'greb+l\ngreb+a\ngrob',
      r: '// l-deletion must come first. Swap the two lines to see the wrong result.\nl > ∅ / [+cons] + _ #\n[-sonorant +voice] > [-voice] / _ (+) #' },
    { label: 'Nasal place assimilation', m: 'sim',
      w: 'anpa\nanka\nanta\nanɟa\nanma',
      r: '// α β γ δ copy a feature value from the next sound\n[+nasal] > [αlabial βalveolar γpalatal δvelar] / _ [+stop αlabial βalveolar γpalatal δvelar]' },
    { label: 'Vowel harmony (needs left-to-right)', m: 'ltr',
      w: 'kitaplar\nkitapler\nevlar\nokulɯ',
      r: '// back harmony passes through any consonants\n[+vowel] > [αback -αfront] / [+vowel αback] [-vowel]* _' }
  ];
  var DEF = { w: PRESETS[0].w, r: PRESETS[0].r, m: 'sim', dots: true };

  function $(id) { return document.getElementById(id); }
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;' }[c]; }); }
  var el = { w: $('words'), r: $('rules'), m: $('mode'), dots: $('dots'), out: $('result'), parsed: $('parsed'), notes: $('notes'), status: $('status') };
  var lastTSV = '';

  function fmt(es) {
    return es.map(function (e) {
      if (e.t === 'sym') return esc(e.seg);
      if (e.t === 'cls' || e.t === 'bnd') return e.v;
      if (e.t === 'mat') return '<span class="mx">' + e.specs.map(function (s) { return '<span>' + (s.pos ? '+' : '−') + (s.a || '') + s.n + '</span>'; }).join('') + '</span>';
      if (e.t === 'opt') return '(' + fmt(e.seq) + ')';
      if (e.t === 'alt') return '{' + e.alts.map(fmt).join(', ') + '}';
      return fmt(e.seq) + '*';
    }).join(' ');
  }
  function fmtRule(r) {
    function sl(x) { return x.length ? fmt(x) : '∅'; }
    return sl(r.T) + ' → ' + sl(r.X) + ' / ' + fmt(r.L) + ' <u>&emsp;</u> ' + fmt(r.R);
  }

  function say(msg) {
    el.status.textContent = msg; clearTimeout(say.t);
    say.t = setTimeout(function () { el.status.textContent = ''; }, 2600);
  }
  function copy(text, msg) {
    var t = document.createElement('textarea');
    t.value = text; t.style.cssText = 'position:fixed;opacity:0';
    document.body.appendChild(t); t.select();
    try { document.execCommand('copy'); say(msg); } catch (e) { say('Copy failed.'); }
    document.body.removeChild(t);
  }

  function run_() {
    var model = compile(el.r.value), words = el.w.value.split(/\s+/).filter(Boolean).slice(0, 500);
    var d = derivation(words, model, el.m.value, el.dots.checked), msgs = model.errors.slice();
    el.parsed.innerHTML = model.rules.map(function (r, i) { return '<li>' + fmtRule(r) + (r.mode ? ' <em>@' + r.mode + '</em>' : '') + '</li>'; }).join('');
    var h = '<table class="dtab"><thead><tr><th>Input</th>' + model.rules.map(function (r, i) { return '<th>' + (i + 1) + '</th>'; }).join('') + '<th>Output</th></tr></thead><tbody>';
    d.rows.forEach(function (row) {
      h += '<tr><td>' + esc(row.input) + '</td>' + row.cells.map(function (c) { return '<td>' + (c === null ? '<span class="same">·</span>' : esc(c)) + '</td>'; }).join('') + '<td><b>' + esc(row.out) + '</b></td></tr>';
    });
    el.out.innerHTML = words.length ? h + '</tbody></table>' : '<p class="out-empty">Type some IPA words on the left.</p>';
    Object.keys(d.notes.msgs).forEach(function (k) { msgs.push(d.notes.msgs[k]); });
    if (d.notes.approx) msgs.push('A changed sound has no exact IPA symbol, so the nearest one was used.');
    var u = Object.keys(UNK);
    if (u.length) msgs.push('No features known for: ' + u.join(' ') + '. Rules that use features cannot match these.');
    el.notes.innerHTML = msgs.map(function (m) { return '<div>' + esc(m) + '</div>'; }).join('');
    el.notes.hidden = !msgs.length;
    lastTSV = d.rows.map(function (r) { return r.input + '\t' + r.out; }).join('\n');
    try {
      var q = new URLSearchParams({ w: el.w.value, r: el.r.value, m: el.m.value, dots: el.dots.checked ? '1' : '0' });
      history.replaceState(null, '', location.pathname + '?' + q.toString());
    } catch (e) { /* sandboxes may refuse */ }
  }

  function write(s) { el.w.value = s.w; el.r.value = s.r; el.m.value = s.m; el.dots.checked = !!s.dots; }
  var timer;
  function schedule() { clearTimeout(timer); timer = setTimeout(run_, 150); }

  PRESETS.forEach(function (p) {
    var b = document.createElement('button');
    b.type = 'button'; b.className = 'btn btn--small'; b.textContent = p.label;
    b.addEventListener('click', function () { write({ w: p.w, r: p.r, m: p.m, dots: true }); run_(); say('Loaded "' + p.label + '".'); });
    $('presets').appendChild(b);
  });
  $('form').addEventListener('input', schedule);
  $('form').addEventListener('change', schedule);
  $('copy-out').addEventListener('click', function () { copy(lastTSV, 'Copied input and output columns.'); });
  $('copy-link').addEventListener('click', function () { clearTimeout(timer); run_(); copy(location.href, 'Link copied.'); });

  var q = new URLSearchParams(location.search), s0 = Object.assign({}, DEF);
  if (q.has('w')) s0.w = q.get('w');
  if (q.has('r')) s0.r = q.get('r');
  if (/^(sim|ltr|rtl)$/.test(q.get('m') || '')) s0.m = q.get('m');
  if (q.has('dots')) s0.dots = q.get('dots') !== '0';
  write(s0);
  run_();
})();