-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B029
-- name    : CK_CKLaneC2R_EpCells_B029
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:11:52.487126+00:00
-- url     : https://prove2.me/theorems/4036e440-3073-4667-9f53-bf85fdfa2d49
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B029` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B029` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B029` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B029 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B029.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B029 =====
section

namespace CKLaneC2R.EpCells.B029

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['125427/819200', '1255119/8192000', '999/1000', '7993/8000']  interval_lower 143502679/1099511627776
noncomputable def e1740 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267688552204,0,true,156492498304,156492498368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931334703348,0,false,-182521858560,-182521858496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267823446509,0,true,156609490688,156609490752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931199809043,0,false,-182681123072,-182681123008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586549228,0,true,74918848,74918912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436706324,0,false,-74924032,-74923968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597313001,0,true,85681856,85681920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425942551,0,false,-85688576,-85688512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621098,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622671,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267772721110,0,true,156565498560,156565498624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931250534442,0,false,-182621230848,-182621230784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267897152324,0,true,156673409728,156673409792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931126103228,0,false,-182768154496,-182768154432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073724101604,0,false,-26094744704,-26094744640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073762199744,0,false,-26055732224,-26055732160⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156492498304,156492498368⟩ : DyadicInterval 40),(⟨-182521858560,-182521858496⟩ : DyadicInterval 40),(⟨749210920012,749210939342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156609490688,156609490752⟩ : DyadicInterval 40),(⟨-182681123072,-182681123008⟩ : DyadicInterval 40),(⟨749190115452,749190134782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74921452,85685225⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74918848,74918912⟩ : DyadicInterval 40),(⟨-74924032,-74923968⟩ : DyadicInterval 40),(⟨762123381038,762123400367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85681856,85681920⟩ : DyadicInterval 40),(⟨-85688576,-85688512⟩ : DyadicInterval 40),(⟨762123380234,762123399563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168261093334,168385524548⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156565498560,156565498624⟩ : DyadicInterval 40),(⟨-182621230848,-182621230784⟩ : DyadicInterval 40),(⟨749197940747,749197960077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156673409728,156673409792⟩ : DyadicInterval 40),(⟨-182768154496,-182768154432⟩ : DyadicInterval 40),(⟨749178740753,749178760082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26094744704,-26055732160⟩ : DyadicInterval 40),(⟨775151249696,775170775232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1740_ok : ecellOkT e1740 = true := by decide +kernel
theorem e1740_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1740 e1740_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '999/1000', '7993/8000']  interval_lower 72257073/549755813888
noncomputable def e1741 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267802389104,0,true,156591228672,156591228736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931220866448,0,false,-182656259904,-182656259840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267937297653,0,true,156708222976,156708223040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931085957899,0,false,-182815560768,-182815560704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586601699,0,true,74971328,74971392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436653853,0,false,-74976512,-74976448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597372973,0,true,85741824,85741888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425882579,0,false,-85748544,-85748480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621089,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622664,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267886614980,0,true,156664271808,156664271872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931136640572,0,false,-182755711616,-182755711552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268011053324,0,true,156772179456,156772179520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931012202228,0,false,-182902661632,-182902661568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073689202898,0,false,-26130482176,-26130482112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073727329003,0,false,-26091439808,-26091439744⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156591228672,156591228736⟩ : DyadicInterval 40),(⟨-182656259904,-182656259840⟩ : DyadicInterval 40),(⟨749193364216,749193383545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156708222976,156708223040⟩ : DyadicInterval 40),(⟨-182815560768,-182815560704⟩ : DyadicInterval 40),(⟨749172543140,749172562469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74973923,85745197⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74971328,74971392⟩ : DyadicInterval 40),(⟨-74976512,-74976448⟩ : DyadicInterval 40),(⟨762123381031,762123400360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85741824,85741888⟩ : DyadicInterval 40),(⟨-85748544,-85748480⟩ : DyadicInterval 40),(⟨762123380224,762123399554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168374987204,168499425548⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156664271808,156664271872⟩ : DyadicInterval 40),(⟨-182755711616,-182755711552⟩ : DyadicInterval 40),(⟨749180367219,749180386549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156772179456,156772179520⟩ : DyadicInterval 40),(⟨-182902661632,-182902661568⟩ : DyadicInterval 40),(⟨749161152919,749161172248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26130482176,-26091439744⟩ : DyadicInterval 40),(⟨775169103488,775188643968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1741_ok : ecellOkT e1741 = true := by decide +kernel
theorem e1741_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1741 e1741_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '7993/8000', '3997/4000']  interval_lower 143357205/1099511627776
noncomputable def e1742 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267709595362,0,true,156510749632,156510749696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931313660190,0,false,-182546701888,-182546701824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267844503911,0,true,156627752448,156627752512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931178751641,0,false,-182705986816,-182705986752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575846266,0,true,64216576,64216640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447409286,0,false,-64220416,-64220352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586602542,0,true,74972160,74972224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436653010,0,false,-74977344,-74977280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622663,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624026,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267783242521,0,true,156574623488,156574623552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931240013031,0,false,-182633653376,-182633653312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267907680880,0,true,156682539968,156682540032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931115574672,0,false,-182780587072,-182780587008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073720876696,0,false,-26098047040,-26098046976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073758979406,0,false,-26059029824,-26059029760⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156510749632,156510749696⟩ : DyadicInterval 40),(⟨-182546701888,-182546701824⟩ : DyadicInterval 40),(⟨749207675669,749207694998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156627752448,156627752512⟩ : DyadicInterval 40),(⟨-182705986816,-182705986752⟩ : DyadicInterval 40),(⟨749186866255,749186885584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64218490,74974766⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64216576,64216640⟩ : DyadicInterval 40),(⟨-64220416,-64220352⟩ : DyadicInterval 40),(⟨762123381721,762123401050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74972160,74972224⟩ : DyadicInterval 40),(⟨-74977344,-74977280⟩ : DyadicInterval 40),(⟨762123381031,762123400360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168271614745,168396053104⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156574623488,156574623552⟩ : DyadicInterval 40),(⟨-182633653376,-182633653312⟩ : DyadicInterval 40),(⟨749196317846,749196337175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156682539968,156682540032⟩ : DyadicInterval 40),(⟨-182780587072,-182780587008⟩ : DyadicInterval 40),(⟨749177115501,749177134830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26098047040,-26059029760⟩ : DyadicInterval 40),(⟨775152898496,775172426400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1742_ok : ecellOkT e1742 = true := by decide +kernel
theorem e1742_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1742 e1742_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '7993/8000', '3997/4000']  interval_lower 144368167/1099511627776
noncomputable def e1743 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267823446506,0,true,156609490688,156609490752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931199809046,0,false,-182681123072,-182681123008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267958369299,0,true,156726495424,156726495488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931064886253,0,false,-182840444352,-182840444288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575891242,0,true,64261568,64261632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447364310,0,false,-64265408,-64265344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586655019,0,true,75024640,75024704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436600533,0,false,-75029824,-75029760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622656,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624020,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267897143512,0,true,156673402112,156673402176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931126112040,0,false,-182768144064,-182768144000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268021589002,0,true,156781315072,156781315136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931001666550,0,false,-182915104192,-182915104128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073685973626,0,false,-26133789120,-26133789056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073724104304,0,false,-26094741952,-26094741888⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156609490688,156609490752⟩ : DyadicInterval 40),(⟨-182681123072,-182681123008⟩ : DyadicInterval 40),(⟨749190115453,749190134782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156726495424,156726495488⟩ : DyadicInterval 40),(⟨-182840444352,-182840444288⟩ : DyadicInterval 40),(⟨749169289515,749169308844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64263466,75027243⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64261568,64261632⟩ : DyadicInterval 40),(⟨-64265408,-64265344⟩ : DyadicInterval 40),(⟨762123381715,762123401045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75024640,75024704⟩ : DyadicInterval 40),(⟨-75029824,-75029760⟩ : DyadicInterval 40),(⟨762123381024,762123400353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168385515736,168509961226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156673402112,156673402176⟩ : DyadicInterval 40),(⟨-182768144064,-182768144000⟩ : DyadicInterval 40),(⟨749178742087,749178761416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156781315072,156781315136⟩ : DyadicInterval 40),(⟨-182915104192,-182915104128⟩ : DyadicInterval 40),(⟨749159525461,749159544790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26133789120,-26094741888⟩ : DyadicInterval 40),(⟨775170754560,775190297440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1743_ok : ecellOkT e1743 = true := by decide +kernel
theorem e1743_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1743 e1743_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '3997/4000', '1599/1600']  interval_lower 141197651/1099511627776
noncomputable def e1744 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267502907745,0,true,156331470400,156331470464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931520347807,0,false,-182302712960,-182302712896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267637802050,0,true,156448480000,156448480064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931385453502,0,false,-182461945728,-182461945664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565068304,0,true,53439168,53439232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458187248,0,false,-53441856,-53441792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575802086,0,true,64172416,64172480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447453466,0,false,-64176192,-64176128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624030,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625179,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267565947716,0,true,156386153856,156386153920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931457307836,0,false,-182377124160,-182377124096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267690378978,0,true,156494082688,156494082752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931332876574,0,false,-182524015168,-182524015104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073787395633,0,false,-26029932480,-26029932416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073825446988,0,false,-25990970240,-25990970176⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156331470400,156331470464⟩ : DyadicInterval 40),(⟨-182302712960,-182302712896⟩ : DyadicInterval 40),(⟨749239524024,749239543353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156448480000,156448480064⟩ : DyadicInterval 40),(⟨-182461945728,-182461945664⟩ : DyadicInterval 40),(⟨749218742738,749218762068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53440528,64174310⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53439168,53439232⟩ : DyadicInterval 40),(⟨-53441856,-53441792⟩ : DyadicInterval 40),(⟨762123382298,762123401627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64172416,64172480⟩ : DyadicInterval 40),(⟨-64176192,-64176128⟩ : DyadicInterval 40),(⟨762123381694,762123401023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168054319940,168178751202⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156386153856,156386153920⟩ : DyadicInterval 40),(⟨-182377124160,-182377124096⟩ : DyadicInterval 40),(⟨749229814477,749229833806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156494082688,156494082752⟩ : DyadicInterval 40),(⟨-182524015168,-182524015104⟩ : DyadicInterval 40),(⟨749210638391,749210657721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26029932480,-25990970176⟩ : DyadicInterval 40),(⟨775118868704,775138369120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1744_ok : ecellOkT e1744 = true := by decide +kernel
theorem e1744_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1744 e1744_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '3997/4000', '1599/1600']  interval_lower 142203573/1099511627776
noncomputable def e1745 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267616773133,0,true,156430239936,156430240000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931406482419,0,false,-182437121152,-182437121088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267751681682,0,true,156547251392,156547251456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931271573870,0,false,-182596390208,-182596390144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565105780,0,true,53476672,53476736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458149772,0,false,-53479360,-53479296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575847061,0,true,64217408,64217472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447408491,0,false,-64221184,-64221120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624025,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625175,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267679856090,0,true,156484955776,156484955840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931343399462,0,false,-182511592192,-182511592128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267804294221,0,true,156592880896,156592880960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931218961331,0,false,-182658509312,-182658509248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073752535408,0,false,-26065628416,-26065628352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073790614647,0,false,-26026636352,-26026636288⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156430239936,156430240000⟩ : DyadicInterval 40),(⟨-182437121152,-182437121088⟩ : DyadicInterval 40),(⟨749221983522,749222002852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156547251392,156547251456⟩ : DyadicInterval 40),(⟨-182596390208,-182596390144⟩ : DyadicInterval 40),(⟨749201185729,749201205059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53478004,64219285⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53476672,53476736⟩ : DyadicInterval 40),(⟨-53479360,-53479296⟩ : DyadicInterval 40),(⟨762123382294,762123401624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64217408,64217472⟩ : DyadicInterval 40),(⟨-64221184,-64221120⟩ : DyadicInterval 40),(⟨762123381689,762123401018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168168228314,168292666445⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156484955776,156484955840⟩ : DyadicInterval 40),(⟨-182511592192,-182511592128⟩ : DyadicInterval 40),(⟨749212260654,749212279984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156592880896,156592880960⟩ : DyadicInterval 40),(⟨-182658509312,-182658509248⟩ : DyadicInterval 40),(⟨749193070307,749193089637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26065628416,-26026636288⟩ : DyadicInterval 40),(⟨775136701760,775156217088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1745_ok : ecellOkT e1745 = true := by decide +kernel
theorem e1745_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1745 e1745_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '1599/1600', '1999/2000']  interval_lower 141052771/1099511627776
noncomputable def e1746 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267523922416,0,true,156349699712,156349699776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931499333136,0,false,-182327517696,-182327517632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267658830965,0,true,156466719680,156466719744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931364424587,0,false,-182486770944,-182486770880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554380239,0,true,42751616,42751680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468875313,0,false,-42753344,-42753280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565106527,0,true,53477440,53477504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458149025,0,false,-53480064,-53480000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625174,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626114,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267576454931,0,true,156395268032,156395268096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931446800621,0,false,-182389527104,-182389527040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267700893331,0,true,156503202112,156503202176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931322362221,0,false,-182536428288,-182536428224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073784179031,0,false,-26033226112,-26033226048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073822234947,0,false,-25994259072,-25994259008⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156349699712,156349699776⟩ : DyadicInterval 40),(⟨-182327517696,-182327517632⟩ : DyadicInterval 40),(⟨749236287687,749236307017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156466719680,156466719744⟩ : DyadicInterval 40),(⟨-182486770944,-182486770880⟩ : DyadicInterval 40),(⟨749215501623,749215520953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42752463,53478751⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42751616,42751680⟩ : DyadicInterval 40),(⟨-42753344,-42753280⟩ : DyadicInterval 40),(⟨762123382753,762123402082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53477440,53477504⟩ : DyadicInterval 40),(⟨-53480064,-53480000⟩ : DyadicInterval 40),(⟨762123382262,762123401591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168064827155,168189265555⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156395268032,156395268096⟩ : DyadicInterval 40),(⟨-182389527104,-182389527040⟩ : DyadicInterval 40),(⟨749228195717,749228215046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156503202112,156503202176⟩ : DyadicInterval 40),(⟨-182536428288,-182536428224⟩ : DyadicInterval 40),(⟨749209017379,749209036709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26033226112,-25994259008⟩ : DyadicInterval 40),(⟨775120513120,775140015936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1746_ok : ecellOkT e1746 = true := by decide +kernel
theorem e1746_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1746 e1746_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '1599/1600', '1999/2000']  interval_lower 142058365/1099511627776
noncomputable def e1747 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267637802048,0,true,156448480000,156448480064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931385453504,0,false,-182461945728,-182461945664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267772724841,0,true,156565501824,156565501888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931250530711,0,false,-182621235264,-182621235200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554410219,0,true,42781568,42781632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468845333,0,false,-42783296,-42783232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565144005,0,true,53514880,53514944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458111547,0,false,-53517568,-53517504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625171,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626112,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267690370428,0,true,156494075264,156494075328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931332885124,0,false,-182524005120,-182524005056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267814815698,0,true,156602005696,156602005760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931208439854,0,false,-182670932352,-182670932288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073749314446,0,false,-26068926656,-26068926592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073787398250,0,false,-26029929792,-26029929728⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156448480000,156448480064⟩ : DyadicInterval 40),(⟨-182461945728,-182461945664⟩ : DyadicInterval 40),(⟨749218742739,749218762068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156565501824,156565501888⟩ : DyadicInterval 40),(⟨-182621235264,-182621235200⟩ : DyadicInterval 40),(⟨749197940161,749197959490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42782443,53516229⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42781568,42781632⟩ : DyadicInterval 40),(⟨-42783296,-42783232⟩ : DyadicInterval 40),(⟨762123382751,762123402080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53514880,53514944⟩ : DyadicInterval 40),(⟨-53517568,-53517504⟩ : DyadicInterval 40),(⟨762123382291,762123401620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168178742652,168303187922⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156494075264,156494075328⟩ : DyadicInterval 40),(⟨-182524005120,-182524005056⟩ : DyadicInterval 40),(⟨749210639734,749210659063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156602005696,156602005760⟩ : DyadicInterval 40),(⟨-182670932352,-182670932288⟩ : DyadicInterval 40),(⟨749191447067,749191466397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26068926656,-26029929728⟩ : DyadicInterval 40),(⟨775138348480,775157866208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1747_ok : ecellOkT e1747 = true := by decide +kernel
theorem e1747_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1747 e1747_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '3997/4000', '1599/1600']  interval_lower 143211625/1099511627776
noncomputable def e1748 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267730638521,0,true,156529000640,156529000704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931292617031,0,false,-182571545792,-182571545728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267865561314,0,true,156646013888,156646013952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931157694238,0,false,-182730851136,-182730851072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565143257,0,true,53514176,53514240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458112295,0,false,-53516800,-53516736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575892037,0,true,64262336,64262400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447363515,0,false,-64266176,-64266112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624019,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625172,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267793763952,0,true,156583748416,156583748480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931229491600,0,false,-182646076032,-182646075968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267918209458,0,true,156691670208,156691670272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931105046094,0,false,-182793019904,-182793019840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073717651580,0,false,-26101349632,-26101349568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073755758861,0,false,-26062327616,-26062327552⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156529000640,156529000704⟩ : DyadicInterval 40),(⟨-182571545792,-182571545728⟩ : DyadicInterval 40),(⟨749204430930,749204450259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156646013888,156646013952⟩ : DyadicInterval 40),(⟨-182730851136,-182730851072⟩ : DyadicInterval 40),(⟨749183616660,749183635989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53515481,64264261⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53514176,53514240⟩ : DyadicInterval 40),(⟨-53516800,-53516736⟩ : DyadicInterval 40),(⟨762123382259,762123401588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64262336,64262400⟩ : DyadicInterval 40),(⟨-64266176,-64266112⟩ : DyadicInterval 40),(⟨762123381715,762123401044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168282136176,168406581682⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156583748416,156583748480⟩ : DyadicInterval 40),(⟨-182646076032,-182646075968⟩ : DyadicInterval 40),(⟨749194694789,749194714119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156691670208,156691670272⟩ : DyadicInterval 40),(⟨-182793019904,-182793019840⟩ : DyadicInterval 40),(⟨749175490148,749175509478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26101349632,-26062327552⟩ : DyadicInterval 40),(⟨775154547392,775174077696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1748_ok : ecellOkT e1748 = true := by decide +kernel
theorem e1748_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1748 e1748_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '3997/4000', '1599/1600']  interval_lower 144222157/1099511627776
noncomputable def e1749 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267844503909,0,true,156627752448,156627752512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931178751643,0,false,-182705986816,-182705986752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267979440945,0,true,156744767552,156744767616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931043814607,0,false,-182865328512,-182865328448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565180738,0,true,53551616,53551680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458074814,0,false,-53554304,-53554240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575937018,0,true,64307328,64307392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447318534,0,false,-64311168,-64311104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624014,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625168,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267907672069,0,true,156682532352,156682532416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931115583483,0,false,-182780576704,-182780576640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268032124701,0,true,156790450624,156790450688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930991130851,0,false,-182927546880,-182927546816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073682744145,0,false,-26137096256,-26137096192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073720879396,0,false,-26098044288,-26098044224⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156627752448,156627752512⟩ : DyadicInterval 40),(⟨-182705986816,-182705986752⟩ : DyadicInterval 40),(⟨749186866255,749186885585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156744767552,156744767616⟩ : DyadicInterval 40),(⟨-182865328512,-182865328448⟩ : DyadicInterval 40),(⟨749166035491,749166054821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53552962,64309242⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53551616,53551680⟩ : DyadicInterval 40),(⟨-53554304,-53554240⟩ : DyadicInterval 40),(⟨762123382287,762123401616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64307328,64307392⟩ : DyadicInterval 40),(⟨-64311168,-64311104⟩ : DyadicInterval 40),(⟨762123381710,762123401039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168396044293,168520496925⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156682532352,156682532416⟩ : DyadicInterval 40),(⟨-182780576704,-182780576640⟩ : DyadicInterval 40),(⟨749177116863,749177136192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156790450624,156790450688⟩ : DyadicInterval 40),(⟨-182927546880,-182927546816⟩ : DyadicInterval 40),(⟨749157897883,749157917212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26137096256,-26098044224⟩ : DyadicInterval 40),(⟨775172405728,775191951008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1749_ok : ecellOkT e1749 = true := by decide +kernel
theorem e1749_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1749 e1749_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '1599/1600', '1999/2000']  interval_lower 143065795/1099511627776
noncomputable def e1750 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267751681680,0,true,156547251392,156547251456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931271573872,0,false,-182596390208,-182596390144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267886618716,0,true,156664275008,156664275072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931136636836,0,false,-182755716032,-182755715968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554440202,0,true,42811584,42811648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468815350,0,false,-42813312,-42813248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565181486,0,true,53552384,53552448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458074066,0,false,-53555072,-53555008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625167,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626109,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267804285413,0,true,156592873280,156592873344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931218970139,0,false,-182658498944,-182658498880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267928738056,0,true,156700800320,156700800384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931094517496,0,false,-182805452800,-182805452736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073714426256,0,false,-26104652480,-26104652416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073752538105,0,false,-26065625600,-26065625536⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156547251392,156547251456⟩ : DyadicInterval 40),(⟨-182596390208,-182596390144⟩ : DyadicInterval 40),(⟨749201185730,749201205059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156664275008,156664275072⟩ : DyadicInterval 40),(⟨-182755716032,-182755715968⟩ : DyadicInterval 40),(⟨749180366667,749180385997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42812426,53553710⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42811584,42811648⟩ : DyadicInterval 40),(⟨-42813312,-42813248⟩ : DyadicInterval 40),(⟨762123382748,762123402078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53552384,53552448⟩ : DyadicInterval 40),(⟨-53555072,-53555008⟩ : DyadicInterval 40),(⟨762123382287,762123401616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168292657637,168417110280⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156592873280,156592873344⟩ : DyadicInterval 40),(⟨-182658498944,-182658498880⟩ : DyadicInterval 40),(⟨749193071667,749193090996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156700800320,156700800384⟩ : DyadicInterval 40),(⟨-182805452800,-182805452736⟩ : DyadicInterval 40),(⟨749173864686,749173884016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26104652480,-26065625536⟩ : DyadicInterval 40),(⟨775156196384,775175729120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1750_ok : ecellOkT e1750 = true := by decide +kernel
theorem e1750_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1750 e1750_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '1599/1600', '1999/2000']  interval_lower 36018973/274877906944
noncomputable def e1751 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267865561312,0,true,156646013888,156646013952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931157694240,0,false,-182730851136,-182730851072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268000512592,0,true,156763039424,156763039488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931022742960,0,false,-182890213248,-182890213184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554470187,0,true,42841536,42841600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468785365,0,false,-42843264,-42843200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565218970,0,true,53589888,53589952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458036582,0,false,-53592512,-53592448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625163,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626107,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267918200646,0,true,156691662528,156691662592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931105054906,0,false,-182793009472,-182793009408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268042660426,0,true,156799586112,156799586176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930980595126,0,false,-182939989824,-182939989760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073679514455,0,false,-26140403648,-26140403584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073717654280,0,false,-26101346880,-26101346816⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156646013888,156646013952⟩ : DyadicInterval 40),(⟨-182730851136,-182730851072⟩ : DyadicInterval 40),(⟨749183616660,749183635990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156763039424,156763039488⟩ : DyadicInterval 40),(⟨-182890213248,-182890213184⟩ : DyadicInterval 40),(⟨749162781032,749162800361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42842411,53591194⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42841536,42841600⟩ : DyadicInterval 40),(⟨-42843264,-42843200⟩ : DyadicInterval 40),(⟨762123382746,762123402075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53589888,53589952⟩ : DyadicInterval 40),(⟨-53592512,-53592448⟩ : DyadicInterval 40),(⟨762123382251,762123401580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168406572870,168531032650⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156691662528,156691662592⟩ : DyadicInterval 40),(⟨-182793009472,-182793009408⟩ : DyadicInterval 40),(⟨749175491520,749175510849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156799586112,156799586176⟩ : DyadicInterval 40),(⟨-182939989824,-182939989760⟩ : DyadicInterval 40),(⟨749156270240,749156289570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26140403648,-26101346816⟩ : DyadicInterval 40),(⟨775174057024,775193604704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1751_ok : ecellOkT e1751 = true := by decide +kernel
theorem e1751_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1751 e1751_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '1999/2000', '7997/8000']  interval_lower 136914515/1099511627776
noncomputable def e1752 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267089361585,0,true,155972675968,155972676032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931933893967,0,false,-181814695808,-181814695744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267224227402,0,true,156089699008,156089699072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931799028150,0,false,-181973824320,-181973824256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543602202,0,true,31973952,31974016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479653350,0,false,-31974912,-31974848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554291009,0,true,42662400,42662464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468964543,0,false,-42664064,-42664000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626120,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626847,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267131272977,0,true,156009043776,156009043840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931891982575,0,false,-181864144704,-181864144640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267255689768,0,true,156116997120,156116997184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931767565784,0,false,-182010950144,-182010950080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073920201889,0,false,-25893953024,-25893952960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073958150444,0,false,-25855100864,-25855100800⟩
    { al := (156147/1024000), au := (50001/327680), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155972675968,155972676032⟩ : DyadicInterval 40),(⟨-181814695808,-181814695744⟩ : DyadicInterval 40),(⟨749303127603,749303146933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156089699008,156089699072⟩ : DyadicInterval 40),(⟨-181973824320,-181973824256⟩ : DyadicInterval 40),(⟨749282402671,749282422000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31974426,42663233⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31973952,31974016⟩ : DyadicInterval 40),(⟨-31974912,-31974848⟩ : DyadicInterval 40),(⟨762123383102,762123402431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42662400,42662464⟩ : DyadicInterval 40),(⟨-42664064,-42664000⟩ : DyadicInterval 40),(⟨762123382728,762123402057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167619645201,167744061992⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156009043776,156009043840⟩ : DyadicInterval 40),(⟨-181864144704,-181864144640⟩ : DyadicInterval 40),(⟨749296688883,749296708212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156116997120,156116997184⟩ : DyadicInterval 40),(⟨-182010950144,-182010950080⟩ : DyadicInterval 40),(⟨749277565374,749277584703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25893953024,-25855100800⟩ : DyadicInterval 40),(⟨775050934016,775070379392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1752_ok : ecellOkT e1752 = true := by decide +kernel
theorem e1752_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1752 e1752_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '1999/2000', '7997/8000']  interval_lower 137908705/1099511627776
noncomputable def e1753 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267203255461,0,true,156071502464,156071502528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931820000091,0,false,-181949077952,-181949077888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267338135522,0,true,156188527360,156188527424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931685120030,0,false,-182108242752,-182108242688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543624682,0,true,31996416,31996480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479630870,0,false,-31997376,-31997312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554320984,0,true,42692352,42692416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468934568,0,false,-42694080,-42694016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626118,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626845,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267245195081,0,true,156107891520,156107891584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931778060471,0,false,-181998566208,-181998566144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267369619255,0,true,156215841536,156215841600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931653636297,0,false,-182145398336,-182145398272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073885427387,0,false,-25929556800,-25929556736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073923403978,0,false,-25890674624,-25890674560⟩
    { al := (50001/327680), au := (625437/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156071502464,156071502528⟩ : DyadicInterval 40),(⟨-181949077952,-181949077888⟩ : DyadicInterval 40),(⟨749285626560,749285645889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156188527360,156188527424⟩ : DyadicInterval 40),(⟨-182108242752,-182108242688⟩ : DyadicInterval 40),(⟨749264885135,749264904465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31996906,42693208⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31996416,31996480⟩ : DyadicInterval 40),(⟨-31997376,-31997312⟩ : DyadicInterval 40),(⟨762123383100,762123402429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42692352,42692416⟩ : DyadicInterval 40),(⟨-42694080,-42694016⟩ : DyadicInterval 40),(⟨762123382758,762123402087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167733567305,167857991479⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156107891520,156107891584⟩ : DyadicInterval 40),(⟨-181998566208,-181998566144⟩ : DyadicInterval 40),(⟨749279179043,749279198372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156215841536,156215841600⟩ : DyadicInterval 40),(⟨-182145398336,-182145398272⟩ : DyadicInterval 40),(⟨749260041227,749260060557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25929556800,-25890674560⟩ : DyadicInterval 40),(⟨775068720896,775088181280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1753_ok : ecellOkT e1753 = true := by decide +kernel
theorem e1753_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1753 e1753_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '7997/8000', '3999/4000']  interval_lower 136770433/1099511627776
noncomputable def e1754 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267110319281,0,true,155990861760,155990861824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931912936271,0,false,-181839422336,-181839422272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267245199342,0,true,156107895232,156107895296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931778056210,0,false,-181998571264,-181998571200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532944020,0,true,21316032,21316096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490311532,0,false,-21316480,-21316416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543625335,0,true,31997056,31997120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479630217,0,false,-31998080,-31998016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626844,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627363,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267141751490,0,true,156018136128,156018136192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931881504062,0,false,-181876508032,-181876507968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267266175680,0,true,156126094976,156126095040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931757079872,0,false,-182023323904,-182023323840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073917002279,0,false,-25897228864,-25897228800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073954955463,0,false,-25858371840,-25858371776⟩
    { al := (156147/1024000), au := (50001/327680), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155990861760,155990861824⟩ : DyadicInterval 40),(⟨-181839422336,-181839422272⟩ : DyadicInterval 40),(⟨749299908138,749299927468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156107895232,156107895296⟩ : DyadicInterval 40),(⟨-181998571264,-181998571200⟩ : DyadicInterval 40),(⟨749279178391,749279197720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21316244,31997559⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21316032,21316096⟩ : DyadicInterval 40),(⟨-21316480,-21316416⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31997056,31997120⟩ : DyadicInterval 40),(⟨-31998080,-31998016⟩ : DyadicInterval 40),(⟨762123383132,762123402461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167630123714,167754547904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156018136128,156018136192⟩ : DyadicInterval 40),(⟨-181876508032,-181876507968⟩ : DyadicInterval 40),(⟨749295078827,749295098156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156126094976,156126095040⟩ : DyadicInterval 40),(⟨-182023323904,-182023323840⟩ : DyadicInterval 40),(⟨749275953000,749275972330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25897228864,-25858371776⟩ : DyadicInterval 40),(⟨775052569504,775072017312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1754_ok : ecellOkT e1754 = true := by decide +kernel
theorem e1754_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1754 e1754_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '7997/8000', '3999/4000']  interval_lower 137764557/1099511627776
noncomputable def e1755 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267224227400,0,true,156089699008,156089699072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931799028152,0,false,-181973824320,-181973824256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267359121705,0,true,156206734272,156206734336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931664133847,0,false,-182133009472,-182133009408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532959006,0,true,21331008,21331072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490296546,0,false,-21331456,-21331392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543647815,0,true,32019520,32019584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479607737,0,false,-32020544,-32020480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626843,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627363,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267255680972,0,true,156116989440,156116989504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931767574580,0,false,-182010939776,-182010939712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267380112289,0,true,156224944768,156224944832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931643143263,0,false,-182157782016,-182157781952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073882223428,0,false,-25932837184,-25932837120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073920204574,0,false,-25893950272,-25893950208⟩
    { al := (50001/327680), au := (625437/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156089699008,156089699072⟩ : DyadicInterval 40),(⟨-181973824320,-181973824256⟩ : DyadicInterval 40),(⟨749282402671,749282422001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156206734272,156206734336⟩ : DyadicInterval 40),(⟨-182133009472,-182133009408⟩ : DyadicInterval 40),(⟨749261656434,749261675764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21331230,32020039⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21331008,21331072⟩ : DyadicInterval 40),(⟨-21331456,-21331392⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32019520,32019584⟩ : DyadicInterval 40),(⟨-32020544,-32020480⟩ : DyadicInterval 40),(⟨762123383131,762123402460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167744053196,167868484513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156116989440,156116989504⟩ : DyadicInterval 40),(⟨-182010939776,-182010939712⟩ : DyadicInterval 40),(⟨749277566759,749277586089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156224944768,156224944832⟩ : DyadicInterval 40),(⟨-182157782016,-182157781952⟩ : DyadicInterval 40),(⟨749258426637,749258445967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25932837184,-25893950208⟩ : DyadicInterval 40),(⟨775070358720,775089821472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1755_ok : ecellOkT e1755 = true := by decide +kernel
theorem e1755_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1755 e1755_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '1999/2000', '7997/8000']  interval_lower 69452955/549755813888
noncomputable def e1756 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267317149336,0,true,156170320064,156170320128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931706106216,0,false,-182083476544,-182083476480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267452043641,0,true,156287346816,156287346880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931571211911,0,false,-182242677632,-182242677568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543647162,0,true,32018880,32018944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479608390,0,false,-32019904,-32019840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554350961,0,true,42722304,42722368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468904591,0,false,-42724032,-42723968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626115,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626844,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267359117440,0,true,156206730624,156206730688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931664138112,0,false,-182133004480,-182133004416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267483548739,0,true,156314677056,156314677120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931539706813,0,false,-182279862976,-182279862912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073850629275,0,false,-25965185856,-25965185792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073888633826,0,false,-25926273856,-25926273792⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156170320064,156170320128⟩ : DyadicInterval 40),(⟨-182083476544,-182083476480⟩ : DyadicInterval 40),(⟨749268113455,749268132785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156287346816,156287346880⟩ : DyadicInterval 40),(⟨-182242677632,-182242677568⟩ : DyadicInterval 40),(⟨749247355532,749247374862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32019386,42723185⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32018880,32018944⟩ : DyadicInterval 40),(⟨-32019904,-32019840⟩ : DyadicInterval 40),(⟨762123383131,762123402460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42722304,42722368⟩ : DyadicInterval 40),(⟨-42724032,-42723968⟩ : DyadicInterval 40),(⟨762123382755,762123402084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167847489664,167971920963⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156206730624,156206730688⟩ : DyadicInterval 40),(⟨-182133004480,-182133004416⟩ : DyadicInterval 40),(⟨749261657078,749261676408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156314677056,156314677120⟩ : DyadicInterval 40),(⟨-182279862976,-182279862912⟩ : DyadicInterval 40),(⟨749242505003,749242524332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25965185856,-25926273792⟩ : DyadicInterval 40),(⟨775086520512,775105995808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1756_ok : ecellOkT e1756 = true := by decide +kernel
theorem e1756_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1756 e1756_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '1999/2000', '7997/8000']  interval_lower 139905535/1099511627776
noncomputable def e1757 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267431043212,0,true,156269128832,156269128896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931592212340,0,false,-182217891584,-182217891520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267565951761,0,true,156386157376,156386157440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931457303791,0,false,-182377128896,-182377128832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543669644,0,true,32041344,32041408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479585908,0,false,-32042368,-32042304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554380940,0,true,42752320,42752384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468874612,0,false,-42754048,-42753984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626113,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626843,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267473039803,0,true,156305560768,156305560832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931550215749,0,false,-182267459136,-182267459072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267597478225,0,true,156413503744,156413503808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931425777327,0,false,-182414344000,-182414343936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073815807552,0,false,-26000840256,-26000840192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073853840067,0,false,-25961898368,-25961898304⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156269128832,156269128896⟩ : DyadicInterval 40),(⟨-182217891584,-182217891520⟩ : DyadicInterval 40),(⟨749250588251,749250607581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156386157376,156386157440⟩ : DyadicInterval 40),(⟨-182377128896,-182377128832⟩ : DyadicInterval 40),(⟨749229813831,749229833161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32041868,42753164⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32041344,32041408⟩ : DyadicInterval 40),(⟨-32042368,-32042304⟩ : DyadicInterval 40),(⟨762123383130,762123402459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42752320,42752384⟩ : DyadicInterval 40),(⟨-42754048,-42753984⟩ : DyadicInterval 40),(⟨762123382753,762123402082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167961412027,168085850449⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156305560768,156305560832⟩ : DyadicInterval 40),(⟨-182267459136,-182267459072⟩ : DyadicInterval 40),(⟨749244123047,749244142377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156413503744,156413503808⟩ : DyadicInterval 40),(⟨-182414344000,-182414343936⟩ : DyadicInterval 40),(⟨749224956634,749224975964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26000840256,-25961898304⟩ : DyadicInterval 40),(⟨775104332768,775123823008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1757_ok : ecellOkT e1757 = true := by decide +kernel
theorem e1757_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1757 e1757_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '7997/8000', '3999/4000']  interval_lower 69380631/549755813888
noncomputable def e1758 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267338135520,0,true,156188527360,156188527424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931685120032,0,false,-182108242752,-182108242688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267473044068,0,true,156305564480,156305564544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931550211484,0,false,-182267464192,-182267464128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532973993,0,true,21345984,21346048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490281559,0,false,-21346432,-21346368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543670298,0,true,32042048,32042112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479585254,0,false,-32043008,-32042944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626842,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627362,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267369610457,0,true,156215833920,156215833984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931653645095,0,false,-182145387968,-182145387904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267494048898,0,true,156323785664,156323785728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931529206654,0,false,-182292256512,-182292256448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073847420965,0,false,-25968470848,-25968470784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073885430074,0,false,-25929554048,-25929553984⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156188527360,156188527424⟩ : DyadicInterval 40),(⟨-182108242752,-182108242688⟩ : DyadicInterval 40),(⟨749264885136,749264904465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156305564480,156305564544⟩ : DyadicInterval 40),(⟨-182267464192,-182267464128⟩ : DyadicInterval 40),(⟨749244122393,749244141723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21346217,32042522⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21345984,21346048⟩ : DyadicInterval 40),(⟨-21346432,-21346368⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32042048,32042112⟩ : DyadicInterval 40),(⟨-32043008,-32042944⟩ : DyadicInterval 40),(⟨762123383098,762123402427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167857982681,167982421122⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156215833920,156215833984⟩ : DyadicInterval 40),(⟨-182145387968,-182145387904⟩ : DyadicInterval 40),(⟨749260042578,749260061907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156323785664,156323785728⟩ : DyadicInterval 40),(⟨-182292256512,-182292256448⟩ : DyadicInterval 40),(⟨749240888166,749240907495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25968470848,-25929553984⟩ : DyadicInterval 40),(⟨775088160608,775107638304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1758_ok : ecellOkT e1758 = true := by decide +kernel
theorem e1758_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1758 e1758_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '7997/8000', '3999/4000']  interval_lower 4367521/34359738368
noncomputable def e1759 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267452043639,0,true,156287346816,156287346880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931571211913,0,false,-182242677632,-182242677568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267586966432,0,true,156404385792,156404385856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931436289120,0,false,-182401935360,-182401935296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532988982,0,true,21360960,21361024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490266570,0,false,-21361472,-21361408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543692783,0,true,32064512,32064576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479562769,0,false,-32065536,-32065472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626840,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627361,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267483539938,0,true,156314669440,156314669504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931539715614,0,false,-182279852544,-182279852480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267607985506,0,true,156422617664,156422617728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931415270046,0,false,-182426747520,-182426747456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073812594888,0,false,-26004129792,-26004129728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073850631965,0,false,-25965183104,-25965183040⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156287346816,156287346880⟩ : DyadicInterval 40),(⟨-182242677632,-182242677568⟩ : DyadicInterval 40),(⟨749247355532,749247374862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156404385792,156404385856⟩ : DyadicInterval 40),(⟨-182401935360,-182401935296⟩ : DyadicInterval 40),(⟨749226576275,749226595604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21361206,32065007⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21360960,21361024⟩ : DyadicInterval 40),(⟨-21361472,-21361408⟩ : DyadicInterval 40),(⟨762123383392,762123402722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32064512,32064576⟩ : DyadicInterval 40),(⟨-32065536,-32065472⟩ : DyadicInterval 40),(⟨762123383128,762123402457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167971912162,168096357730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156314669440,156314669504⟩ : DyadicInterval 40),(⟨-182279852544,-182279852480⟩ : DyadicInterval 40),(⟨749242506328,749242525658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156422617664,156422617728⟩ : DyadicInterval 40),(⟨-182426747520,-182426747456⟩ : DyadicInterval 40),(⟨749223337639,749223356968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26004129792,-25965183040⟩ : DyadicInterval 40),(⟨775105975136,775125467776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1759_ok : ecellOkT e1759 = true := by decide +kernel
theorem e1759_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1759 e1759_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '3999/4000', '7999/8000']  interval_lower 136626973/1099511627776
noncomputable def e1760 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267131276976,0,true,156009047296,156009047360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931891978576,0,false,-181864149376,-181864149312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267266171281,0,true,156126091136,156126091200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931757084271,0,false,-182023318720,-182023318656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522285792,0,true,10657920,10657984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500969760,0,false,-10658112,-10658048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532959613,0,true,21331584,21331648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490295939,0,false,-21332096,-21332032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627362,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267152230543,0,true,156027228864,156027228928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931871025009,0,false,-181888872192,-181888872128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267276661617,0,true,156135192768,156135192832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931746593935,0,false,-182035697792,-182035697728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073913802460,0,false,-25900504960,-25900504896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073951760117,0,false,-25861643264,-25861643200⟩
    { al := (156147/1024000), au := (50001/327680), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156009047296,156009047360⟩ : DyadicInterval 40),(⟨-181864149376,-181864149312⟩ : DyadicInterval 40),(⟨749296688220,749296707549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156126091136,156126091200⟩ : DyadicInterval 40),(⟨-182023318720,-182023318656⟩ : DyadicInterval 40),(⟨749275953694,749275973023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10658016,21331837⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10657920,10657984⟩ : DyadicInterval 40),(⟨-10658112,-10658048⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21331584,21331648⟩ : DyadicInterval 40),(⟨-21332096,-21332032⟩ : DyadicInterval 40),(⟨762123383394,762123402723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167640602767,167765033841⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156027228864,156027228928⟩ : DyadicInterval 40),(⟨-181888872192,-181888872128⟩ : DyadicInterval 40),(⟨749293468614,749293487944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156135192768,156135192832⟩ : DyadicInterval 40),(⟨-182035697792,-182035697728⟩ : DyadicInterval 40),(⟨749274340510,749274359839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25900504960,-25861643200⟩ : DyadicInterval 40),(⟨775054205216,775073655360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1760_ok : ecellOkT e1760 = true := by decide +kernel
theorem e1760_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1760 e1760_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '3999/4000', '7999/8000']  interval_lower 137620501/1099511627776
noncomputable def e1761 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267245199340,0,true,156107895232,156107895296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931778056212,0,false,-181998571200,-181998571136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267380107888,0,true,156224940928,156224940992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931643147664,0,false,-182157776832,-182157776768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522293285,0,true,10665408,10665472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500962267,0,false,-10665600,-10665536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532974601,0,true,21346560,21346624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490280951,0,false,-21347072,-21347008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627361,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267266166888,0,true,156126087360,156126087424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931757088664,0,false,-182023313536,-182023313472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267390605346,0,true,156234047936,156234048000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931632650206,0,false,-182170165824,-182170165760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073879019263,0,false,-25936117824,-25936117760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073917004962,0,false,-25897226176,-25897226112⟩
    { al := (50001/327680), au := (625437/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156107895232,156107895296⟩ : DyadicInterval 40),(⟨-181998571200,-181998571136⟩ : DyadicInterval 40),(⟨749279178364,749279197693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156224940928,156224940992⟩ : DyadicInterval 40),(⟨-182157776832,-182157776768⟩ : DyadicInterval 40),(⟨749258427332,749258446661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10665509,21346825⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10665408,10665472⟩ : DyadicInterval 40),(⟨-10665600,-10665536⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21346560,21346624⟩ : DyadicInterval 40),(⟨-21347072,-21347008⟩ : DyadicInterval 40),(⟨762123383393,762123402722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167754539112,167878977570⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156126087360,156126087424⟩ : DyadicInterval 40),(⟨-182023313536,-182023313472⟩ : DyadicInterval 40),(⟨749275954349,749275973678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156234047936,156234048000⟩ : DyadicInterval 40),(⟨-182170165824,-182170165760⟩ : DyadicInterval 40),(⟨749256811930,749256831259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25936117824,-25897226112⟩ : DyadicInterval 40),(⟨775071996672,775091461792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1761_ok : ecellOkT e1761 = true := by decide +kernel
theorem e1761_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1761 e1761_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '7999/8000', '1']  interval_lower 34120703/274877906944
noncomputable def e1762 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267152234672,0,true,156027232448,156027232512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931871020880,0,false,-181888877056,-181888876992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522293846,0,true,10665984,10666048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500961706,0,false,-10666176,-10666112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267162709096,0,true,156036321152,156036321216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931860546456,0,false,-181901235840,-181901235776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287147576,0,true,156144290560,156144290624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931736107976,0,false,-182048071872,-182048071808⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073910602436,0,false,-25903781312,-25903781248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073948564724,0,false,-25864914688,-25864914624⟩
    { al := (156147/1024000), au := (50001/327680), zl := (7999/8000), zu := 1,
      A := ⟨167661564592,167775515444⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156027232448,156027232512⟩ : DyadicInterval 40),(⟨-181888877056,-181888876992⟩ : DyadicInterval 40),(⟨749293467976,749293487305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10666070⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10665984,10666048⟩ : DyadicInterval 40),(⟨-10666176,-10666112⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167651081320,167775519800⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156036321152,156036321216⟩ : DyadicInterval 40),(⟨-181901235840,-181901235776⟩ : DyadicInterval 40),(⟨749291858315,749291877645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144290560,156144290624⟩ : DyadicInterval 40),(⟨-182048071872,-182048071808⟩ : DyadicInterval 40),(⟨749272727892,749272747222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25903781312,-25864914624⟩ : DyadicInterval 40),(⟨775055840928,775075293536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1762_ok : ecellOkT e1762 = true := by decide +kernel
theorem e1762_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1762 e1762_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '7999/8000', '1']  interval_lower 17184515/137438953472
noncomputable def e1763 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267266171279,0,true,156126091136,156126091200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931757084273,0,false,-182023318720,-182023318656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522301340,0,true,10673472,10673536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500954212,0,false,-10673664,-10673600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267276652821,0,true,156135185152,156135185216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931746602731,0,false,-182035687424,-182035687360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401098427,0,true,156243151040,156243151104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931622157125,0,false,-182182549824,-182182549760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073875814890,0,false,-25939398720,-25939398656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073913805146,0,false,-25900502208,-25900502144⟩
    { al := (50001/327680), au := (625437/4096000), zl := (7999/8000), zu := 1,
      A := ⟨167775515443,167889466295⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156126091136,156126091200⟩ : DyadicInterval 40),(⟨-182023318720,-182023318656⟩ : DyadicInterval 40),(⟨749275953694,749275973023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10673564⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10673472,10673536⟩ : DyadicInterval 40),(⟨-10673664,-10673600⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167765025045,167889470651⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156135185152,156135185216⟩ : DyadicInterval 40),(⟨-182035687424,-182035687360⟩ : DyadicInterval 40),(⟨749274341858,749274361188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243151040,156243151104⟩ : DyadicInterval 40),(⟨-182182549824,-182182549760⟩ : DyadicInterval 40),(⟨749255197132,749255216462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25939398720,-25900502144⟩ : DyadicInterval 40),(⟨775073634688,775093102240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1763_ok : ecellOkT e1763 = true := by decide +kernel
theorem e1763_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1763 e1763_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '3999/4000', '7999/8000']  interval_lower 138616655/1099511627776
noncomputable def e1764 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267359121703,0,true,156206734272,156206734336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931664133849,0,false,-182133009472,-182133009408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267494044495,0,true,156323781824,156323781888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931529211057,0,false,-182292251328,-182292251264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522300779,0,true,10672896,10672960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500954773,0,false,-10673088,-10673024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532989590,0,true,21361600,21361664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490265962,0,false,-21362048,-21361984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627360,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267380103491,0,true,156224937152,156224937216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931643152061,0,false,-182157771584,-182157771520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267504549077,0,true,156332894208,156332894272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931518706475,0,false,-182304650304,-182304650240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073844212448,0,false,-25971756032,-25971755968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073882226116,0,false,-25932834432,-25932834368⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156206734272,156206734336⟩ : DyadicInterval 40),(⟨-182133009472,-182133009408⟩ : DyadicInterval 40),(⟨749261656435,749261675764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156323781824,156323781888⟩ : DyadicInterval 40),(⟨-182292251328,-182292251264⟩ : DyadicInterval 40),(⟨749240888861,749240908190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10673003,21361814⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10672896,10672960⟩ : DyadicInterval 40),(⟨-10673088,-10673024⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21361600,21361664⟩ : DyadicInterval 40),(⟨-21362048,-21361984⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167868475715,167992921301⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156224937152,156224937216⟩ : DyadicInterval 40),(⟨-182157771584,-182157771520⟩ : DyadicInterval 40),(⟨749258427961,749258447291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156332894208,156332894272⟩ : DyadicInterval 40),(⟨-182304650304,-182304650240⟩ : DyadicInterval 40),(⟨749239271266,749239290595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25971756032,-25932834368⟩ : DyadicInterval 40),(⟨775089800800,775109280896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1764_ok : ecellOkT e1764 = true := by decide +kernel
theorem e1764_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1764 e1764_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '3999/4000', '7999/8000']  interval_lower 139615585/1099511627776
noncomputable def e1765 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267473044066,0,true,156305564480,156305564544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931550211486,0,false,-182267464192,-182267464128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267607981103,0,true,156422613888,156422613952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931415274449,0,false,-182426742336,-182426742272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522308273,0,true,10680384,10680448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500947279,0,false,-10680576,-10680512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533004579,0,true,21376576,21376640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490250973,0,false,-21377024,-21376960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627360,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267494040097,0,true,156323778048,156323778112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931529215455,0,false,-182292246144,-182292246080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267618492810,0,true,156431731584,156431731648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931404762742,0,false,-182439151232,-182439151168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073809382017,0,false,-26007419584,-26007419520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073847423655,0,false,-25968468096,-25968468032⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156305564480,156305564544⟩ : DyadicInterval 40),(⟨-182267464192,-182267464128⟩ : DyadicInterval 40),(⟨749244122393,749244141723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156422613888,156422613952⟩ : DyadicInterval 40),(⟨-182426742336,-182426742272⟩ : DyadicInterval 40),(⟨749223338298,749223357627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10680497,21376803⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10680384,10680448⟩ : DyadicInterval 40),(⟨-10680576,-10680512⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21376576,21376640⟩ : DyadicInterval 40),(⟨-21377024,-21376960⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167982412321,168106865034⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156323778048,156323778112⟩ : DyadicInterval 40),(⟨-182292246144,-182292246080⟩ : DyadicInterval 40),(⟨749240889519,749240908848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156431731584,156431731648⟩ : DyadicInterval 40),(⟨-182439151232,-182439151168⟩ : DyadicInterval 40),(⟨749221718515,749221737845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26007419584,-25968468032⟩ : DyadicInterval 40),(⟨775107617632,775127112672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1765_ok : ecellOkT e1765 = true := by decide +kernel
theorem e1765_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1765 e1765_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '7999/8000', '1']  interval_lower 17309019/137438953472
noncomputable def e1766 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267380107886,0,true,156224940928,156224940992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931643147666,0,false,-182157776768,-182157776704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522308834,0,true,10680960,10681024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500946718,0,false,-10681152,-10681088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267390596550,0,true,156234040320,156234040384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931632659002,0,false,-182170155456,-182170155392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515049281,0,true,156342002688,156342002752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931508206271,0,false,-182317044224,-182317044160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073841003724,0,false,-25975041472,-25975041408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073879021950,0,false,-25936115072,-25936115008⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (7999/8000), zu := 1,
      A := ⟨167889466294,168003417146⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156224940928,156224940992⟩ : DyadicInterval 40),(⟨-182157776768,-182157776704⟩ : DyadicInterval 40),(⟨749258427305,749258446634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10681058⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10680960,10681024⟩ : DyadicInterval 40),(⟨-10681152,-10681088⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167878968774,168003421505⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156234040320,156234040384⟩ : DyadicInterval 40),(⟨-182170155456,-182170155392⟩ : DyadicInterval 40),(⟨749256813281,749256832610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156342002688,156342002752⟩ : DyadicInterval 40),(⟨-182317044224,-182317044160⟩ : DyadicInterval 40),(⟨749237654247,749237673577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25975041472,-25936115008⟩ : DyadicInterval 40),(⟨775091441120,775110923616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1766_ok : ecellOkT e1766 = true := by decide +kernel
theorem e1766_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1766 e1766_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '7999/8000', '1']  interval_lower 139470873/1099511627776
noncomputable def e1767 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267494044493,0,true,156323781824,156323781888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931529211059,0,false,-182292251328,-182292251264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522316329,0,true,10688448,10688512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500939223,0,false,-10688640,-10688576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267504540276,0,true,156332886592,156332886656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931518715276,0,false,-182304639872,-182304639808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267629000133,0,true,156440845440,156440845504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931394255419,0,false,-182451555008,-182451554944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073806168939,0,false,-26010709568,-26010709504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073844215139,0,false,-25971753280,-25971753216⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (7999/8000), zu := 1,
      A := ⟨168003417145,168117367997⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156323781824,156323781888⟩ : DyadicInterval 40),(⟨-182292251328,-182292251264⟩ : DyadicInterval 40),(⟨749240888861,749240908191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10688553⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10688448,10688512⟩ : DyadicInterval 40),(⟨-10688640,-10688576⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167992912500,168117372357⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156332886592,156332886656⟩ : DyadicInterval 40),(⟨-182304639872,-182304639808⟩ : DyadicInterval 40),(⟨749239272592,749239291921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440845440,156440845504⟩ : DyadicInterval 40),(⟨-182451555008,-182451554944⟩ : DyadicInterval 40),(⟨749220099247,749220118576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26010709568,-25971753216⟩ : DyadicInterval 40),(⟨775109260224,775128757664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1767_ok : ecellOkT e1767 = true := by decide +kernel
theorem e1767_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1767 e1767_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '1999/2000', '7997/8000']  interval_lower 35226979/274877906944
noncomputable def e1768 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267544937087,0,true,156367928704,156367928768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931478318465,0,false,-182352323008,-182352322944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267679859880,0,true,156484959104,156484959168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931343395672,0,false,-182511596672,-182511596608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543692128,0,true,32063872,32063936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479563424,0,false,-32064832,-32064768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554410920,0,true,42782272,42782336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468844632,0,false,-42784000,-42783936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626111,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626841,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267586962422,0,true,156404382272,156404382336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931436293130,0,false,-182401930624,-182401930560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267711407711,0,true,156512321536,156512321600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931311847841,0,false,-182548841536,-182548841472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073780962219,0,false,-26036520000,-26036519936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073819022621,0,false,-25997548288,-25997548224⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156367928704,156367928768⟩ : DyadicInterval 40),(⟨-182352323008,-182352322944⟩ : DyadicInterval 40),(⟨749233050956,749233070286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156484959104,156484959168⟩ : DyadicInterval 40),(⟨-182511596672,-182511596608⟩ : DyadicInterval 40),(⟨749212260049,749212279379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32064352,42783144⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32063872,32063936⟩ : DyadicInterval 40),(⟨-32064832,-32064768⟩ : DyadicInterval 40),(⟨762123383096,762123402425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42782272,42782336⟩ : DyadicInterval 40),(⟨-42784000,-42783936⟩ : DyadicInterval 40),(⟨762123382751,762123402080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168075334646,168199779935⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156404382272,156404382336⟩ : DyadicInterval 40),(⟨-182401930624,-182401930560⟩ : DyadicInterval 40),(⟨749226576916,749226596245⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156512321536,156512321600⟩ : DyadicInterval 40),(⟨-182548841536,-182548841472⟩ : DyadicInterval 40),(⟨749207396212,749207415542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26036520000,-25997548224⟩ : DyadicInterval 40),(⟨775122157728,775141662880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1768_ok : ecellOkT e1768 = true := by decide +kernel
theorem e1768_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1768 e1768_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '1999/2000', '7997/8000']  interval_lower 141912287/1099511627776
noncomputable def e1769 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267658830963,0,true,156466719680,156466719744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931364424589,0,false,-182486770944,-182486770880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267793767999,0,true,156583751936,156583752000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931229487553,0,false,-182646080832,-182646080768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543714614,0,true,32086336,32086400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479540938,0,false,-32087360,-32087296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554440904,0,true,42812288,42812352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468814648,0,false,-42814016,-42813952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626108,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626840,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267700884525,0,true,156503194496,156503194560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931322371027,0,false,-182536417920,-182536417856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267825337198,0,true,156611130432,156611130496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931197918354,0,false,-182683355520,-182683355456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073746093275,0,false,-26072225088,-26072225024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073784181726,0,false,-26033223360,-26033223296⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156466719680,156466719744⟩ : DyadicInterval 40),(⟨-182486770944,-182486770880⟩ : DyadicInterval 40),(⟨749215501623,749215520953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156583751936,156583752000⟩ : DyadicInterval 40),(⟨-182646080832,-182646080768⟩ : DyadicInterval 40),(⟨749194694168,749194713498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32086838,42813128⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32086336,32086400⟩ : DyadicInterval 40),(⟨-32087360,-32087296⟩ : DyadicInterval 40),(⟨762123383127,762123402456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42812288,42812352⟩ : DyadicInterval 40),(⟨-42814016,-42813952⟩ : DyadicInterval 40),(⟨762123382748,762123402077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168189256749,168313709422⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156503194496,156503194560⟩ : DyadicInterval 40),(⟨-182536417920,-182536417856⟩ : DyadicInterval 40),(⟨749209018737,749209038067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156611130432,156611130496⟩ : DyadicInterval 40),(⟨-182683355520,-182683355456⟩ : DyadicInterval 40),(⟨749189823709,749189843038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26072225088,-26033223296⟩ : DyadicInterval 40),(⟨775139995264,775159515424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1769_ok : ecellOkT e1769 = true := by decide +kernel
theorem e1769_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1769 e1769_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '7997/8000', '3999/4000']  interval_lower 35190593/274877906944
noncomputable def e1770 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267565951758,0,true,156386157376,156386157440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931457303794,0,false,-182377128896,-182377128832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267700888795,0,true,156503198208,156503198272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931322366757,0,false,-182536422912,-182536422848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533003971,0,true,21375936,21376000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490251581,0,false,-21376448,-21376384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543715268,0,true,32086976,32087040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479540284,0,false,-32088000,-32087936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626839,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627361,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267597469422,0,true,156413496064,156413496128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931425786130,0,false,-182414333632,-182414333568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267721922115,0,true,156521440832,156521440896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931301333437,0,false,-182561254976,-182561254912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073777745198,0,false,-26039814144,-26039814080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073815810244,0,false,-26000837504,-26000837440⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156386157376,156386157440⟩ : DyadicInterval 40),(⟨-182377128896,-182377128832⟩ : DyadicInterval 40),(⟨749229813832,749229833161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156503198208,156503198272⟩ : DyadicInterval 40),(⟨-182536422912,-182536422848⟩ : DyadicInterval 40),(⟨749209018053,749209037382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21376195,32087492⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21375936,21376000⟩ : DyadicInterval 40),(⟨-21376448,-21376384⟩ : DyadicInterval 40),(⟨762123383392,762123402721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32086976,32087040⟩ : DyadicInterval 40),(⟨-32088000,-32087936⟩ : DyadicInterval 40),(⟨762123383127,762123402456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168085841646,168210294339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156413496064,156413496128⟩ : DyadicInterval 40),(⟨-182414333632,-182414333568⟩ : DyadicInterval 40),(⟨749224958026,749224977356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156521440832,156521440896⟩ : DyadicInterval 40),(⟨-182561254976,-182561254912⟩ : DyadicInterval 40),(⟨749205774991,749205794320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26039814144,-26000837440⟩ : DyadicInterval 40),(⟨775123802336,775143309952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1770_ok : ecellOkT e1770 = true := by decide +kernel
theorem e1770_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1770 e1770_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '7997/8000', '3999/4000']  interval_lower 141766755/1099511627776
noncomputable def e1771 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267679859878,0,true,156484959104,156484959168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931343395674,0,false,-182511596672,-182511596608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267814811158,0,true,156602001728,156602001792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931208444394,0,false,-182670926976,-182670926912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533018961,0,true,21390976,21391040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490236591,0,false,-21391424,-21391360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543737756,0,true,32109504,32109568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479517796,0,false,-32110464,-32110400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626838,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627360,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267711398905,0,true,156512313856,156512313920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931311856647,0,false,-182548831168,-182548831104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267835858720,0,true,156620255104,156620255168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931187396832,0,false,-182695778880,-182695778816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073742871896,0,false,-26075523776,-26075523712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073780964914,0,false,-26036517248,-26036517184⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156484959104,156484959168⟩ : DyadicInterval 40),(⟨-182511596672,-182511596608⟩ : DyadicInterval 40),(⟨749212260049,749212279379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156602001728,156602001792⟩ : DyadicInterval 40),(⟨-182670926976,-182670926912⟩ : DyadicInterval 40),(⟨749191447779,749191467109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21391185,32109980⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21390976,21391040⟩ : DyadicInterval 40),(⟨-21391424,-21391360⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32109504,32109568⟩ : DyadicInterval 40),(⟨-32110464,-32110400⟩ : DyadicInterval 40),(⟨762123383094,762123402423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168199771129,168324230944⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156512313856,156512313920⟩ : DyadicInterval 40),(⟨-182548831168,-182548831104⟩ : DyadicInterval 40),(⟨749207397607,749207416936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156620255104,156620255168⟩ : DyadicInterval 40),(⟨-182695778880,-182695778816⟩ : DyadicInterval 40),(⟨749188200258,749188219588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26075523776,-26036517184⟩ : DyadicInterval 40),(⟨775141642208,775161164768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1771_ok : ecellOkT e1771 = true := by decide +kernel
theorem e1771_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1771 e1771_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '1999/2000', '7997/8000']  interval_lower 142919735/1099511627776
noncomputable def e1772 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267772724839,0,true,156565501824,156565501888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931250530713,0,false,-182621235264,-182621235200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267907676119,0,true,156682535872,156682535936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931115579433,0,false,-182780581504,-182780581440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543737101,0,true,32108800,32108864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479518451,0,false,-32109824,-32109760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554470889,0,true,42842240,42842304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468784663,0,false,-42843968,-42843904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626106,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626839,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267814806889,0,true,156601998016,156601998080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931208448663,0,false,-182670921920,-182670921856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267939266680,0,true,156709930432,156709930496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931083988872,0,false,-182817885952,-182817885888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073711200722,0,false,-26107955520,-26107955456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073749317143,0,false,-26068923840,-26068923776⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156565501824,156565501888⟩ : DyadicInterval 40),(⟨-182621235264,-182621235200⟩ : DyadicInterval 40),(⟨749197940161,749197959490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156682535872,156682535936⟩ : DyadicInterval 40),(⟨-182780581504,-182780581440⟩ : DyadicInterval 40),(⟨749177116240,749177135570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32109325,42843113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32108800,32108864⟩ : DyadicInterval 40),(⟨-32109824,-32109760⟩ : DyadicInterval 40),(⟨762123383126,762123402455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42842240,42842304⟩ : DyadicInterval 40),(⟨-42843968,-42843904⟩ : DyadicInterval 40),(⟨762123382746,762123402075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168303179113,168427638904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156601998016,156601998080⟩ : DyadicInterval 40),(⟨-182670921920,-182670921856⟩ : DyadicInterval 40),(⟨749191448436,749191467766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156709930432,156709930496⟩ : DyadicInterval 40),(⟨-182817885952,-182817885888⟩ : DyadicInterval 40),(⟨749172239123,749172258453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26107955520,-26068923776⟩ : DyadicInterval 40),(⟨775157845504,775177380640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1772_ok : ecellOkT e1772 = true := by decide +kernel
theorem e1772_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1772 e1772_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '1999/2000', '7997/8000']  interval_lower 143930115/1099511627776
noncomputable def e1773 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267886618714,0,true,156664275008,156664275072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931136636838,0,false,-182755716032,-182755715968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268021584238,0,true,156781310976,156781311040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931001671314,0,false,-182915098560,-182915098496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543759589,0,true,32131328,32131392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479495963,0,false,-32132288,-32132224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554500875,0,true,42872256,42872320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468754677,0,false,-42873984,-42873920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626104,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626837,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267928729500,0,true,156700792896,156700792960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931094526052,0,false,-182805442752,-182805442688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268053196170,0,true,156808721536,156808721600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930970059382,0,false,-182952432832,-182952432768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073676284557,0,false,-26143711232,-26143711168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073714428878,0,false,-26104649792,-26104649728⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156664275008,156664275072⟩ : DyadicInterval 40),(⟨-182755716032,-182755715968⟩ : DyadicInterval 40),(⟨749180366668,749180385997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156781310976,156781311040⟩ : DyadicInterval 40),(⟨-182915098560,-182915098496⟩ : DyadicInterval 40),(⟨749159526174,749159545503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32131813,42873099⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32131328,32131392⟩ : DyadicInterval 40),(⟨-32132288,-32132224⟩ : DyadicInterval 40),(⟨762123383092,762123402422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42872256,42872320⟩ : DyadicInterval 40),(⟨-42873984,-42873920⟩ : DyadicInterval 40),(⟨762123382744,762123402073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168417101724,168541568394⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156700792896,156700792960⟩ : DyadicInterval 40),(⟨-182805442752,-182805442688⟩ : DyadicInterval 40),(⟨749173866034,749173885363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156808721536,156808721600⟩ : DyadicInterval 40),(⟨-182952432832,-182952432768⟩ : DyadicInterval 40),(⟨749154642452,749154661781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26143711232,-26104649728⟩ : DyadicInterval 40),(⟨775175708480,775195258496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1773_ok : ecellOkT e1773 = true := by decide +kernel
theorem e1773_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1773 e1773_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '7997/8000', '3999/4000']  interval_lower 35693499/274877906944
noncomputable def e1774 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267793767997,0,true,156583751936,156583752000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931229487555,0,false,-182646080832,-182646080768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267928733522,0,true,156700796416,156700796480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931094522030,0,false,-182805447488,-182805447424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533033953,0,true,21405952,21406016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490221599,0,false,-21406400,-21406336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543760244,0,true,32131968,32132032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479495308,0,false,-32132992,-32132928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626836,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627360,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267825328390,0,true,156611122752,156611122816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931197927162,0,false,-182683345152,-182683345088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267949795326,0,true,156719060416,156719060480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931073460226,0,false,-182830319232,-182830319168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073707974980,0,false,-26111258752,-26111258688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073746095972,0,false,-26072222336,-26072222272⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156583751936,156583752000⟩ : DyadicInterval 40),(⟨-182646080832,-182646080768⟩ : DyadicInterval 40),(⟨749194694168,749194713498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156700796416,156700796480⟩ : DyadicInterval 40),(⟨-182805447488,-182805447424⟩ : DyadicInterval 40),(⟨749173865389,749173884718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21406177,32132468⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21405952,21406016⟩ : DyadicInterval 40),(⟨-21406400,-21406336⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32131968,32132032⟩ : DyadicInterval 40),(⟨-32132992,-32132928⟩ : DyadicInterval 40),(⟨762123383124,762123402453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168313700614,168438167550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156611122752,156611122816⟩ : DyadicInterval 40),(⟨-182683345152,-182683345088⟩ : DyadicInterval 40),(⟨749189825105,749189844434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156719060416,156719060480⟩ : DyadicInterval 40),(⟨-182830319232,-182830319168⟩ : DyadicInterval 40),(⟨749170613477,749170632807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26111258752,-26072222272⟩ : DyadicInterval 40),(⟨775159494752,775179032256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1774_ok : ecellOkT e1774 = true := by decide +kernel
theorem e1774_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1774 e1774_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '7997/8000', '3999/4000']  interval_lower 35945933/274877906944
noncomputable def e1775 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267907676117,0,true,156682535872,156682535936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931115579435,0,false,-182780581504,-182780581440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268042655885,0,true,156799582208,156799582272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930980599667,0,false,-182939984448,-182939984384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533048945,0,true,21420928,21420992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490206607,0,false,-21421440,-21421376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543782735,0,true,32154432,32154496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479472817,0,false,-32155456,-32155392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626835,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627359,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267939257868,0,true,156709922752,156709922816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931083997684,0,false,-182817875520,-182817875456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268063731935,0,true,156817856960,156817857024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930959523617,0,false,-182964876096,-182964876032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073673054450,0,false,-26147019072,-26147019008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073711203423,0,false,-26107952768,-26107952704⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156682535872,156682535936⟩ : DyadicInterval 40),(⟨-182780581504,-182780581440⟩ : DyadicInterval 40),(⟨749177116241,749177135570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156799582208,156799582272⟩ : DyadicInterval 40),(⟨-182939984448,-182939984384⟩ : DyadicInterval 40),(⟨749156270917,749156290247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21421169,32154959⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21420928,21420992⟩ : DyadicInterval 40),(⟨-21421440,-21421376⟩ : DyadicInterval 40),(⟨762123383390,762123402719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32154432,32154496⟩ : DyadicInterval 40),(⟨-32155456,-32155392⟩ : DyadicInterval 40),(⟨762123383123,762123402452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168427630092,168552104159⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156709922752,156709922816⟩ : DyadicInterval 40),(⟨-182817875520,-182817875456⟩ : DyadicInterval 40),(⟨749172240495,749172259824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156817856960,156817857024⟩ : DyadicInterval 40),(⟨-182964876096,-182964876032⟩ : DyadicInterval 40),(⟨749153014561,749153033891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26147019072,-26107952704⟩ : DyadicInterval 40),(⟨775177359968,775196912416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1775_ok : ecellOkT e1775 = true := by decide +kernel
theorem e1775_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1775 e1775_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '3999/4000', '7999/8000']  interval_lower 140617525/1099511627776
noncomputable def e1776 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267586966429,0,true,156404385792,156404385856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931436289123,0,false,-182401935360,-182401935296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267721917710,0,true,156521436992,156521437056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931301337842,0,false,-182561249792,-182561249728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522315768,0,true,10687936,10688000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500939784,0,false,-10688064,-10688000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533019569,0,true,21391552,21391616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490235983,0,false,-21392064,-21392000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627359,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267607976958,0,true,156422610240,156422610304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931415278594,0,false,-182426737472,-182426737408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267732436536,0,true,156530560064,156530560128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931290819016,0,false,-182573668544,-182573668480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073774527971,0,false,-26043108480,-26043108416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073812597503,0,false,-26004127168,-26004127104⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156404385792,156404385856⟩ : DyadicInterval 40),(⟨-182401935360,-182401935296⟩ : DyadicInterval 40),(⟨749226576275,749226595605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156521436992,156521437056⟩ : DyadicInterval 40),(⟨-182561249792,-182561249728⟩ : DyadicInterval 40),(⟨749205775688,749205795018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10687992,21391793⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10687936,10688000⟩ : DyadicInterval 40),(⟨-10688064,-10688000⟩ : DyadicInterval 40),(⟨762123383512,762123402841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21391552,21391616⟩ : DyadicInterval 40),(⟨-21392064,-21392000⟩ : DyadicInterval 40),(⟨762123383391,762123402720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168096349182,168220808760⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156422610240,156422610304⟩ : DyadicInterval 40),(⟨-182426737472,-182426737408⟩ : DyadicInterval 40),(⟨749223338979,749223358309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156530560064,156530560128⟩ : DyadicInterval 40),(⟨-182573668544,-182573668480⟩ : DyadicInterval 40),(⟨749204153652,749204172981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26043108480,-26004127104⟩ : DyadicInterval 40),(⟨775125447168,775144957120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1776_ok : ecellOkT e1776 = true := by decide +kernel
theorem e1776_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1776 e1776_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '3999/4000', '7999/8000']  interval_lower 70810645/549755813888
noncomputable def e1777 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267700888793,0,true,156503198208,156503198272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931322366759,0,false,-182536422912,-182536422848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267835854317,0,true,156620251264,156620251328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931187401235,0,false,-182695773696,-182695773632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522323264,0,true,10695424,10695488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500932288,0,false,-10695552,-10695488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533034561,0,true,21406528,21406592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490220991,0,false,-21407040,-21406976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627359,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267721913309,0,true,156521433152,156521433216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931301342243,0,false,-182561244608,-182561244544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267846380267,0,true,156629379712,156629379776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931176875285,0,false,-182708202432,-182708202368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073739650308,0,false,-26078822656,-26078822592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073777747894,0,false,-26039811392,-26039811328⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156503198208,156503198272⟩ : DyadicInterval 40),(⟨-182536422912,-182536422848⟩ : DyadicInterval 40),(⟨749209018053,749209037382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156620251264,156620251328⟩ : DyadicInterval 40),(⟨-182695773696,-182695773632⟩ : DyadicInterval 40),(⟨749188200957,749188220286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10695488,21406785⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10695424,10695488⟩ : DyadicInterval 40),(⟨-10695552,-10695488⟩ : DyadicInterval 40),(⟨762123383511,762123402840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21406528,21406592⟩ : DyadicInterval 40),(⟨-21407040,-21406976⟩ : DyadicInterval 40),(⟨762123383391,762123402720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168210285533,168334752491⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156521433152,156521433216⟩ : DyadicInterval 40),(⟨-182561244608,-182561244544⟩ : DyadicInterval 40),(⟨749205776385,749205795715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156629379712,156629379776⟩ : DyadicInterval 40),(⟨-182708202432,-182708202368⟩ : DyadicInterval 40),(⟨749186576717,749186596046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26078822656,-26039811328⟩ : DyadicInterval 40),(⟨775143289280,775162814208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1777_ok : ecellOkT e1777 = true := by decide +kernel
theorem e1777_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1777 e1777_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '7999/8000', '1']  interval_lower 8779505/68719476736
noncomputable def e1778 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267607981100,0,true,156422613888,156422613952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931415274452,0,false,-182426742336,-182426742272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522323824,0,true,10695936,10696000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500931728,0,false,-10696128,-10696064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267618484005,0,true,156431723968,156431724032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931404771547,0,false,-182439140800,-182439140736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742950984,0,true,156539679296,156539679360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931280304568,0,false,-182586082304,-182586082240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073771310535,0,false,-26046403008,-26046402944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073809384710,0,false,-26007416832,-26007416768⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (7999/8000), zu := 1,
      A := ⟨168117367996,168231318848⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156422613888,156422613952⟩ : DyadicInterval 40),(⟨-182426742336,-182426742272⟩ : DyadicInterval 40),(⟨749223338299,749223357628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10696048⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10695936,10696000⟩ : DyadicInterval 40),(⟨-10696128,-10696064⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168106856229,168231323208⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156431723968,156431724032⟩ : DyadicInterval 40),(⟨-182439140800,-182439140736⟩ : DyadicInterval 40),(⟨749221719843,749221739173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539679296,156539679360⟩ : DyadicInterval 40),(⟨-182586082304,-182586082240⟩ : DyadicInterval 40),(⟨749202532183,749202551513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26046403008,-26007416768⟩ : DyadicInterval 40),(⟨775127092000,775146604384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1778_ok : ecellOkT e1778 = true := by decide +kernel
theorem e1778_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1778 e1778_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '7999/8000', '1']  interval_lower 141475707/1099511627776
noncomputable def e1779 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267721917708,0,true,156521436992,156521437056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931301337844,0,false,-182561249792,-182561249728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522331321,0,true,10703488,10703552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500924231,0,false,-10703616,-10703552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267732427730,0,true,156530552448,156530552512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931290827822,0,false,-182573658176,-182573658112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856901836,0,true,156638504256,156638504320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931166353716,0,false,-182720626112,-182720626048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073736428512,0,false,-26082121792,-26082121728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073774530667,0,false,-26043105728,-26043105664⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (7999/8000), zu := 1,
      A := ⟨168231318847,168345269699⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156521436992,156521437056⟩ : DyadicInterval 40),(⟨-182561249792,-182561249728⟩ : DyadicInterval 40),(⟨749205775689,749205795018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10703545⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10703488,10703552⟩ : DyadicInterval 40),(⟨-10703616,-10703552⟩ : DyadicInterval 40),(⟨762123383511,762123402840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168220799954,168345274060⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156530552448,156530552512⟩ : DyadicInterval 40),(⟨-182573658176,-182573658112⟩ : DyadicInterval 40),(⟨749204155009,749204174339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638504256,156638504320⟩ : DyadicInterval 40),(⟨-182720626112,-182720626048⟩ : DyadicInterval 40),(⟨749184953056,749184972386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26082121792,-26043105664⟩ : DyadicInterval 40),(⟨775144936448,775164463776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1779_ok : ecellOkT e1779 = true := by decide +kernel
theorem e1779_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1779 e1779_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '3999/4000', '7999/8000']  interval_lower 142627977/1099511627776
noncomputable def e1780 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267814811156,0,true,156602001728,156602001792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931208444396,0,false,-182670926976,-182670926912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267949790924,0,true,156719056640,156719056704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931073464628,0,false,-182830314048,-182830313984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522330759,0,true,10702912,10702976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500924793,0,false,-10703040,-10702976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533049554,0,true,21421568,21421632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490205998,0,false,-21422016,-21421952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627358,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267835849911,0,true,156620247424,156620247488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931187405641,0,false,-182695768448,-182695768384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267960323994,0,true,156728190400,156728190464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931062931558,0,false,-182842752704,-182842752640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073704749030,0,false,-26114562240,-26114562176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073742874594,0,false,-26075521024,-26075520960⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168345269698,168459220550⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156602001728,156602001792⟩ : DyadicInterval 40),(⟨-182670926976,-182670926912⟩ : DyadicInterval 40),(⟨749191447780,749191467109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156719056640,156719056704⟩ : DyadicInterval 40),(⟨-182830314048,-182830313984⟩ : DyadicInterval 40),(⟨749170614139,749170633469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10702983,21421778⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10702912,10702976⟩ : DyadicInterval 40),(⟨-10703040,-10702976⟩ : DyadicInterval 40),(⟨762123383511,762123402840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21421568,21421632⟩ : DyadicInterval 40),(⟨-21422016,-21421952⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168324222135,168448696218⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156620247424,156620247488⟩ : DyadicInterval 40),(⟨-182695768448,-182695768384⟩ : DyadicInterval 40),(⟨749188201628,749188220958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156728190400,156728190464⟩ : DyadicInterval 40),(⟨-182842752704,-182842752640⟩ : DyadicInterval 40),(⟨749168987703,749169007032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26114562240,-26075520960⟩ : DyadicInterval 40),(⟨775161144096,775180684000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1780_ok : ecellOkT e1780 = true := by decide +kernel
theorem e1780_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1780 e1780_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '3999/4000', '7999/8000']  interval_lower 71818627/549755813888
noncomputable def e1781 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267928733519,0,true,156700796416,156700796480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931094522033,0,false,-182805447488,-182805447424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268063727531,0,true,156817853120,156817853184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930959528021,0,false,-182964870848,-182964870784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522338256,0,true,10710400,10710464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500917296,0,false,-10710592,-10710528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533064548,0,true,21436544,21436608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490191004,0,false,-21436992,-21436928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627358,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267949786514,0,true,156719052800,156719052864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931073469038,0,false,-182830308800,-182830308736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268074267724,0,true,156826992256,156826992320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930948987828,0,false,-182977319424,-182977319360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073669824134,0,false,-26150327168,-26150327104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073707977681,0,false,-26111256000,-26111255936⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168459220549,168573171401⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156700796416,156700796480⟩ : DyadicInterval 40),(⟨-182805447488,-182805447424⟩ : DyadicInterval 40),(⟨749173865389,749173884718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156817853120,156817853184⟩ : DyadicInterval 40),(⟨-182964870848,-182964870784⟩ : DyadicInterval 40),(⟨749153015234,749153034564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10710480,21436772⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10710400,10710464⟩ : DyadicInterval 40),(⟨-10710592,-10710528⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21436544,21436608⟩ : DyadicInterval 40),(⟨-21436992,-21436928⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168438158738,168562639948⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156719052800,156719052864⟩ : DyadicInterval 40),(⟨-182830308800,-182830308736⟩ : DyadicInterval 40),(⟨749170614812,749170634142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156826992256,156826992320⟩ : DyadicInterval 40),(⟨-182977319424,-182977319360⟩ : DyadicInterval 40),(⟨749151386562,749151405891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26150327168,-26111255936⟩ : DyadicInterval 40),(⟨775179011584,775198566464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1781_ok : ecellOkT e1781 = true := by decide +kernel
theorem e1781_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1781 e1781_ok ha1 ha2 hz1 hz2 hz

-- box ['125427/819200', '1255119/8192000', '7999/8000', '1']  interval_lower 142481989/1099511627776
noncomputable def e1782 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897474,0,true,156638500480,156638500544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358078,0,false,-182720620928,-182720620864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848326,0,true,156737316544,156737316608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407226,0,false,-182855181184,-182855181120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267835854315,0,true,156620251264,156620251328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931187401237,0,false,-182695773696,-182695773632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522338817,0,true,10710976,10711040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500916735,0,false,-10711104,-10711040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267846371457,0,true,156629372032,156629372096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931176884095,0,false,-182708192000,-182708191936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970852682,0,true,156737320320,156737320384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931052402870,0,false,-182855186304,-182855186240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073701522872,0,false,-26117865920,-26117865856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073739653007,0,false,-26078819904,-26078819840⟩
    { al := (125427/819200), au := (1255119/8192000), zl := (7999/8000), zu := 1,
      A := ⟨168345269698,168459220550⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156620251264,156620251328⟩ : DyadicInterval 40),(⟨-182695773696,-182695773632⟩ : DyadicInterval 40),(⟨749188200957,749188220286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362492,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10711041⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10710976,10711040⟩ : DyadicInterval 40),(⟨-10711104,-10711040⟩ : DyadicInterval 40),(⟨762123383511,762123402840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168334743681,168459224906⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156629372032,156629372096⟩ : DyadicInterval 40),(⟨-182708192000,-182708191936⟩ : DyadicInterval 40),(⟨749186578087,749186597416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737320320,156737320384⟩ : DyadicInterval 40),(⟨-182855186304,-182855186240⟩ : DyadicInterval 40),(⟨749167361811,749167381140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26117865920,-26078819840⟩ : DyadicInterval 40),(⟨775162793536,775182335840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156638500480,156737316608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182855181184,-182720620864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1782_ok : ecellOkT e1782 = true := by decide +kernel
theorem e1782_pos {a z : ℝ} (ha1 : ((125427/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1255119/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1782 e1782_ok ha1 ha2 hz1 hz2 hz

-- box ['1255119/8192000', '39249/256000', '7999/8000', '1']  interval_lower 35872755/274877906944
noncomputable def e1783 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267970848325,0,true,156737316544,156737316608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931052407227,0,false,-182855181184,-182855181120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799177,0,true,156836123776,156836123840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456375,0,false,-182989757888,-182989757824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267949790922,0,true,156719056640,156719056704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931073464630,0,false,-182830314048,-182830313984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522346314,0,true,10718464,10718528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500909238,0,false,-10718592,-10718528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267960315182,0,true,156728182784,156728182848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931062940370,0,false,-182842742272,-182842742208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084803535,0,true,156836127552,156836127616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930938452017,0,false,-182989763008,-182989762944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073666593610,0,false,-26153635456,-26153635392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073704751731,0,false,-26114559488,-26114559424⟩
    { al := (1255119/8192000), au := (39249/256000), zl := (7999/8000), zu := 1,
      A := ⟨168459220549,168573171401⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156737316544,156737316608⟩ : DyadicInterval 40),(⟨-182855181184,-182855181120⟩ : DyadicInterval 40),(⟨749167362493,749167381822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156719056640,156719056704⟩ : DyadicInterval 40),(⟨-182830314048,-182830313984⟩ : DyadicInterval 40),(⟨749170614140,749170633469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757888,-182989757824⟩ : DyadicInterval 40),(⟨749149759143,749149778473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10718538⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10718464,10718528⟩ : DyadicInterval 40),(⟨-10718592,-10718528⟩ : DyadicInterval 40),(⟨762123383511,762123402840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168448687406,168573175759⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156728182784,156728182848⟩ : DyadicInterval 40),(⟨-182842742272,-182842742208⟩ : DyadicInterval 40),(⟨749168989038,749169008368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836127552,156836127616⟩ : DyadicInterval 40),(⟨-182989763008,-182989762944⟩ : DyadicInterval 40),(⟨749149758460,749149777789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26153635456,-26114559424⟩ : DyadicInterval 40),(⟨775180663328,775200220608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156737316544,156836123840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182989757888,-182855181120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1783_ok : ecellOkT e1783 = true := by decide +kernel
theorem e1783_pos {a z : ℝ} (ha1 : ((1255119/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((39249/256000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1783 e1783_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '999/1000', '7993/8000']  interval_lower 4547761/34359738368
noncomputable def e1784 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267916226004,0,true,156689950208,156689950272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931107029548,0,false,-182790677696,-182790677632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268051148797,0,true,156806946304,156806946368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930972106755,0,false,-182950014848,-182950014784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586654176,0,true,75023808,75023872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436601376,0,false,-75028992,-75028928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597432950,0,true,85801792,85801856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425822602,0,false,-85808576,-85808512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621079,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622657,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268000508860,0,true,156763036160,156763036224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931022746692,0,false,-182890208832,-182890208768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268124954323,0,true,156870940288,156870940352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930898301229,0,false,-183037185280,-183037185216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073654280594,0,false,-26166244928,-26166244864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073692434662,0,false,-26127172672,-26127172608⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156689950208,156689950272⟩ : DyadicInterval 40),(⟨-182790677696,-182790677632⟩ : DyadicInterval 40),(⟨749175796340,749175815669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156806946304,156806946368⟩ : DyadicInterval 40),(⟨-182950014848,-182950014784⟩ : DyadicInterval 40),(⟨749154958786,749154978116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75026400,85805174⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75023808,75023872⟩ : DyadicInterval 40),(⟨-75028992,-75028928⟩ : DyadicInterval 40),(⟨762123381024,762123400353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85801792,85801856⟩ : DyadicInterval 40),(⟨-85808576,-85808512⟩ : DyadicInterval 40),(⟨762123380247,762123399577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168488881084,168613326547⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156763036160,156763036224⟩ : DyadicInterval 40),(⟨-182890208832,-182890208768⟩ : DyadicInterval 40),(⟨749162781620,749162800950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156870940288,156870940352⟩ : DyadicInterval 40),(⟨-183037185280,-183037185216⟩ : DyadicInterval 40),(⟨749143553040,749143572369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26166244928,-26127172608⟩ : DyadicInterval 40),(⟨775186969920,775206525344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1784_ok : ecellOkT e1784 = true := by decide +kernel
theorem e1784_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1784 e1784_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '999/1000', '7993/8000']  interval_lower 146545025/1099511627776
noncomputable def e1785 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268030062904,0,true,156788662848,156788662912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930993192648,0,false,-182925111936,-182925111872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268164999941,0,true,156905660800,156905660864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930858255611,0,false,-183084485376,-183084485312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586706655,0,true,75076288,75076352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436548897,0,false,-75081472,-75081408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597492931,0,true,85861760,85861824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425762621,0,false,-85868544,-85868480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621070,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622650,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268114402730,0,true,156861791680,156861791744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930908852822,0,false,-183024722560,-183024722496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268238855322,0,true,156969692288,156969692352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930784400230,0,false,-183171725376,-183171725312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073619334692,0,false,-26202033024,-26202032960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073657516729,0,false,-26162930880,-26162930816⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156788662848,156788662912⟩ : DyadicInterval 40),(⟨-182925111936,-182925111872⟩ : DyadicInterval 40),(⟨749158216418,749158235748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156905660800,156905660864⟩ : DyadicInterval 40),(⟨-183084485376,-183084485312⟩ : DyadicInterval 40),(⟨749137362344,749137381673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75078879,85865155⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75076288,75076352⟩ : DyadicInterval 40),(⟨-75081472,-75081408⟩ : DyadicInterval 40),(⟨762123381017,762123400346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85861760,85861824⟩ : DyadicInterval 40),(⟨-85868544,-85868480⟩ : DyadicInterval 40),(⟨762123380238,762123399567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168602774954,168727227546⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156861791680,156861791744⟩ : DyadicInterval 40),(⟨-183024722560,-183024722496⟩ : DyadicInterval 40),(⟨749145183944,749145203274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156969692288,156969692352⟩ : DyadicInterval 40),(⟨-183171725376,-183171725312⟩ : DyadicInterval 40),(⟨749125941050,749125960379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26202033024,-26162930816⟩ : DyadicInterval 40),(⟨775204849024,775224419392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1785_ok : ecellOkT e1785 = true := by decide +kernel
theorem e1785_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1785 e1785_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '7993/8000', '3997/4000']  interval_lower 145381755/1099511627776
noncomputable def e1786 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267937297650,0,true,156708222912,156708222976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931085957902,0,false,-182815560768,-182815560704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268072234687,0,true,156825229504,156825229568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930951020865,0,false,-182974918336,-182974918272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575936222,0,true,64306560,64306624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447319330,0,false,-64310336,-64310272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586707499,0,true,75077120,75077184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436548053,0,false,-75082304,-75082240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622649,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624015,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268011044509,0,true,156772171840,156772171904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931012211043,0,false,-182902651264,-182902651200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268135497123,0,true,156880081280,156880081344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930887758429,0,false,-183049637760,-183049637696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073651046955,0,false,-26169556416,-26169556352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073689205601,0,false,-26130479360,-26130479296⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156708222912,156708222976⟩ : DyadicInterval 40),(⟨-182815560768,-182815560704⟩ : DyadicInterval 40),(⟨749172543177,749172562507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156825229504,156825229568⟩ : DyadicInterval 40),(⟨-182974918336,-182974918272⟩ : DyadicInterval 40),(⟨749151700718,749151720047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64308446,75079723⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64306560,64306624⟩ : DyadicInterval 40),(⟨-64310336,-64310272⟩ : DyadicInterval 40),(⟨762123381678,762123401007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75077120,75077184⟩ : DyadicInterval 40),(⟨-75082304,-75082240⟩ : DyadicInterval 40),(⟨762123381017,762123400346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168499416733,168623869347⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156772171840,156772171904⟩ : DyadicInterval 40),(⟨-182902651264,-182902651200⟩ : DyadicInterval 40),(⟨749161154283,749161173612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156880081280,156880081344⟩ : DyadicInterval 40),(⟨-183049637760,-183049637696⟩ : DyadicInterval 40),(⟨749141923344,749141942673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26169556416,-26130479296⟩ : DyadicInterval 40),(⟨775188623264,775208181088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1786_ok : ecellOkT e1786 = true := by decide +kernel
theorem e1786_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1786 e1786_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '7993/8000', '3997/4000']  interval_lower 2287475/17179869184
noncomputable def e1787 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268051148794,0,true,156806946304,156806946368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930972106758,0,false,-182950014848,-182950014784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268186100075,0,true,156923954688,156923954752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930837155477,0,false,-183109408704,-183109408640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575981204,0,true,64351488,64351552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447274348,0,false,-64355328,-64355264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586759982,0,true,75129600,75129664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436495570,0,false,-75134784,-75134720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622642,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624010,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268124945761,0,true,156870932864,156870932928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930898309791,0,false,-183037175168,-183037175104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268249405245,0,true,156978838592,156978838656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930773850307,0,false,-183184187776,-183184187712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073616096682,0,false,-26205349120,-26205349056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073654283221,0,false,-26166242240,-26166242176⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156806946304,156806946368⟩ : DyadicInterval 40),(⟨-182950014848,-182950014784⟩ : DyadicInterval 40),(⟨749154958787,749154978116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156923954688,156923954752⟩ : DyadicInterval 40),(⟨-183109408704,-183109408640⟩ : DyadicInterval 40),(⟨749134099835,749134119164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64353428,75132206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64351488,64351552⟩ : DyadicInterval 40),(⟨-64355328,-64355264⟩ : DyadicInterval 40),(⟨762123381705,762123401034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75129600,75129664⟩ : DyadicInterval 40),(⟨-75134784,-75134720⟩ : DyadicInterval 40),(⟨762123381009,762123400339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168613317985,168737777469⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156870932864,156870932928⟩ : DyadicInterval 40),(⟨-183037175168,-183037175104⟩ : DyadicInterval 40),(⟨749143554364,749143573693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156978838592,156978838656⟩ : DyadicInterval 40),(⟨-183184187776,-183184187712⟩ : DyadicInterval 40),(⟨749124309150,749124328480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26205349120,-26166242176⟩ : DyadicInterval 40),(⟨775206504704,775226077440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1787_ok : ecellOkT e1787 = true := by decide +kernel
theorem e1787_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1787 e1787_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '999/1000', '7993/8000']  interval_lower 147564295/1099511627776
noncomputable def e1788 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268143899804,0,true,156887366656,156887366720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930879355748,0,false,-183059562560,-183059562496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268278851085,0,true,157004366464,157004366528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930744404467,0,false,-183218972352,-183218972288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586759139,0,true,75128768,75128832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436496413,0,false,-75133952,-75133888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597552916,0,true,85921728,85921792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425702636,0,false,-85928512,-85928448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621061,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622643,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268228296609,0,true,156960538304,156960538368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930794958943,0,false,-183159252672,-183159252608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268352756318,0,true,157068435392,157068435456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930670499234,0,false,-183306281920,-183306281856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073584365192,0,false,-26237846464,-26237846400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073622575198,0,false,-26198714368,-26198714304⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156887366656,156887366720⟩ : DyadicInterval 40),(⟨-183059562560,-183059562496⟩ : DyadicInterval 40),(⟨749140624388,749140643717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157004366464,157004366528⟩ : DyadicInterval 40),(⟨-183218972352,-183218972288⟩ : DyadicInterval 40),(⟨749119753811,749119773140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75131363,85925140⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75128768,75128832⟩ : DyadicInterval 40),(⟨-75133952,-75133888⟩ : DyadicInterval 40),(⟨762123381009,762123400339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85921728,85921792⟩ : DyadicInterval 40),(⟨-85928512,-85928448⟩ : DyadicInterval 40),(⟨762123380228,762123399558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168716668833,168841128542⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156960538304,156960538368⟩ : DyadicInterval 40),(⟨-183159252672,-183159252608⟩ : DyadicInterval 40),(⟨749127574169,749127593498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157068435392,157068435456⟩ : DyadicInterval 40),(⟨-183306281920,-183306281856⟩ : DyadicInterval 40),(⟨749108316985,749108336314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26237846464,-26198714304⟩ : DyadicInterval 40),(⟨775222740768,775242326112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1788_ok : ecellOkT e1788 = true := by decide +kernel
theorem e1788_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1788 e1788_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '999/1000', '7993/8000']  interval_lower 148586195/1099511627776
noncomputable def e1789 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268257736705,0,true,156986061568,156986061632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930765518847,0,false,-183194029696,-183194029632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268392702229,0,true,157103063232,157103063296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930630553323,0,false,-183353475776,-183353475712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586811625,0,true,75181248,75181312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436443927,0,false,-75186432,-75186368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597612907,0,true,85981760,85981824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425642645,0,false,-85988544,-85988480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621051,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622635,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268342190733,0,true,157059276224,157059276288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930681064819,0,false,-183293799616,-183293799552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268466657320,0,true,157167169664,157167169728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930556598232,0,false,-183440854912,-183440854848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073549372091,0,false,-26273685248,-26273685184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073587609996,0,false,-26234523328,-26234523264⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156986061568,156986061632⟩ : DyadicInterval 40),(⟨-183194029696,-183194029632⟩ : DyadicInterval 40),(⟨749123020337,749123039667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157103063232,157103063296⟩ : DyadicInterval 40),(⟨-183353475776,-183353475712⟩ : DyadicInterval 40),(⟨749102133224,749102152553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75183849,85985131⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75181248,75181312⟩ : DyadicInterval 40),(⟨-75186432,-75186368⟩ : DyadicInterval 40),(⟨762123381002,762123400332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85981760,85981824⟩ : DyadicInterval 40),(⟨-85988544,-85988480⟩ : DyadicInterval 40),(⟨762123380219,762123399548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168830562957,168955029544⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157059276224,157059276288⟩ : DyadicInterval 40),(⟨-183293799616,-183293799552⟩ : DyadicInterval 40),(⟨749109952335,749109971664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157167169664,157167169728⟩ : DyadicInterval 40),(⟨-183440854912,-183440854848⟩ : DyadicInterval 40),(⟨749090680805,749090700135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26273685248,-26234523264⟩ : DyadicInterval 40),(⟨775240645248,775260245504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1789_ok : ecellOkT e1789 = true := by decide +kernel
theorem e1789_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1789 e1789_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '7993/8000', '3997/4000']  interval_lower 73708603/549755813888
noncomputable def e1790 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268164999938,0,true,156905660800,156905660864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930858255614,0,false,-183084485376,-183084485312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268299965463,0,true,157022671040,157022671104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930723290089,0,false,-183243915584,-183243915520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576026191,0,true,64396480,64396544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447229361,0,false,-64400320,-64400256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586812471,0,true,75182080,75182144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436443081,0,false,-75187328,-75187264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622634,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624005,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268238846503,0,true,156969684672,156969684736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930784409049,0,false,-183171714944,-183171714880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268363313360,0,true,157077587072,157077587136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930659942192,0,false,-183318754240,-183318754176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073581122809,0,false,-26241167168,-26241167104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073619337399,0,false,-26202030272,-26202030208⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156905660800,156905660864⟩ : DyadicInterval 40),(⟨-183084485376,-183084485312⟩ : DyadicInterval 40),(⟨749137362344,749137381673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157022671040,157022671104⟩ : DyadicInterval 40),(⟨-183243915584,-183243915520⟩ : DyadicInterval 40),(⟨749116486883,749116506213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64398415,75184695⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64396480,64396544⟩ : DyadicInterval 40),(⟨-64400320,-64400256⟩ : DyadicInterval 40),(⟨762123381700,762123401029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75182080,75182144⟩ : DyadicInterval 40),(⟨-75187328,-75187264⟩ : DyadicInterval 40),(⟨762123381034,762123400364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168727218727,168851685584⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156969684672,156969684736⟩ : DyadicInterval 40),(⟨-183171714944,-183171714880⟩ : DyadicInterval 40),(⟨749125942390,749125961720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157077587072,157077587136⟩ : DyadicInterval 40),(⟨-183318754240,-183318754176⟩ : DyadicInterval 40),(⟨749106682842,749106702172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26241167168,-26202030208⟩ : DyadicInterval 40),(⟨775224398720,775243986464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1790_ok : ecellOkT e1790 = true := by decide +kernel
theorem e1790_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1790 e1790_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '7993/8000', '3997/4000']  interval_lower 74219375/549755813888
noncomputable def e1791 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268278851082,0,true,157004366464,157004366528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930744404470,0,false,-183218972352,-183218972288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268413830851,0,true,157121378496,157121378560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930609424701,0,false,-183378438848,-183378438784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576071179,0,true,64441472,64441536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447184373,0,false,-64445312,-64445248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586864962,0,true,75234560,75234624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436390590,0,false,-75239808,-75239744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622627,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623999,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268352747496,0,true,157068427776,157068427840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930670508056,0,false,-183306271488,-183306271424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268477221484,0,true,157176326656,157176326720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930546034068,0,false,-183453337216,-183453337152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073546125333,0,false,-26277010496,-26277010432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073584367902,0,false,-26237843712,-26237843648⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157004366464,157004366528⟩ : DyadicInterval 40),(⟨-183218972352,-183218972288⟩ : DyadicInterval 40),(⟨749119753811,749119773141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157121378496,157121378560⟩ : DyadicInterval 40),(⟨-183378438848,-183378438784⟩ : DyadicInterval 40),(⟨749098861843,749098881173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64443403,75237186⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64441472,64441536⟩ : DyadicInterval 40),(⟨-64445312,-64445248⟩ : DyadicInterval 40),(⟨762123381694,762123401024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75234560,75234624⟩ : DyadicInterval 40),(⟨-75239808,-75239744⟩ : DyadicInterval 40),(⟨762123381027,762123400356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168841119720,168965593708⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157068427776,157068427840⟩ : DyadicInterval 40),(⟨-183306271488,-183306271424⟩ : DyadicInterval 40),(⟨749108318328,749108337657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157176326656,157176326720⟩ : DyadicInterval 40),(⟨-183453337216,-183453337152⟩ : DyadicInterval 40),(⟨749089044481,749089063810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26277010496,-26237843648⟩ : DyadicInterval 40),(⟨775242305440,775261908128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1791_ok : ecellOkT e1791 = true := by decide +kernel
theorem e1791_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1791 e1791_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '3997/4000', '1599/1600']  interval_lower 18154459/137438953472
noncomputable def e1792 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267958369297,0,true,156726495424,156726495488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931064886255,0,false,-182840444352,-182840444288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268093320577,0,true,156843512320,156843512384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930929934975,0,false,-182999822336,-182999822272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565218221,0,true,53589120,53589184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458037331,0,false,-53591808,-53591744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575982001,0,true,64352320,64352384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447273551,0,false,-64356160,-64356096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624009,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625164,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268021580191,0,true,156781307456,156781307520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931001675361,0,false,-182915093760,-182915093696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268146039943,0,true,156889222208,156889222272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930877215609,0,false,-183062090432,-183062090368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073647813107,0,false,-26172868160,-26172868096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073685976328,0,false,-26133786304,-26133786240⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156726495424,156726495488⟩ : DyadicInterval 40),(⟨-182840444352,-182840444288⟩ : DyadicInterval 40),(⟨749169289515,749169308844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156843512320,156843512384⟩ : DyadicInterval 40),(⟨-182999822336,-182999822272⟩ : DyadicInterval 40),(⟨749148442259,749148461588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53590445,64354225⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53589120,53589184⟩ : DyadicInterval 40),(⟨-53591808,-53591744⟩ : DyadicInterval 40),(⟨762123382283,762123401613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64352320,64352384⟩ : DyadicInterval 40),(⟨-64356160,-64356096⟩ : DyadicInterval 40),(⟨762123381705,762123401034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168509952415,168634412167⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156781307456,156781307520⟩ : DyadicInterval 40),(⟨-182915093760,-182915093696⟩ : DyadicInterval 40),(⟨749159526796,749159546126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156889222208,156889222272⟩ : DyadicInterval 40),(⟨-183062090432,-183062090368⟩ : DyadicInterval 40),(⟨749140293556,749140312886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26172868160,-26133786240⟩ : DyadicInterval 40),(⟨775190276736,775209836960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1792_ok : ecellOkT e1792 = true := by decide +kernel
theorem e1792_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1792 e1792_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '3997/4000', '1599/1600']  interval_lower 146251553/1099511627776
noncomputable def e1793 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268072234685,0,true,156825229504,156825229568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930951020867,0,false,-182974918272,-182974918208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268207200209,0,true,156942248256,156942248320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930816055343,0,false,-183134332608,-183134332544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565255707,0,true,53626560,53626624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457999845,0,false,-53629248,-53629184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576026987,0,true,64397312,64397376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447228565,0,false,-64401152,-64401088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624004,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625161,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268135488310,0,true,156880073664,156880073728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930887767242,0,false,-183049627328,-183049627264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268259955188,0,true,156987984896,156987984960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930763300364,0,false,-183196650368,-183196650304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073612858463,0,false,-26208665472,-26208665408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073651049659,0,false,-26169553664,-26169553600⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156825229504,156825229568⟩ : DyadicInterval 40),(⟨-182974918272,-182974918208⟩ : DyadicInterval 40),(⟨749151700691,749151720021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156942248256,156942248320⟩ : DyadicInterval 40),(⟨-183134332608,-183134332544⟩ : DyadicInterval 40),(⟨749130836925,749130856255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53627931,64399211⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53626560,53626624⟩ : DyadicInterval 40),(⟨-53629248,-53629184⟩ : DyadicInterval 40),(⟨762123382280,762123401609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64397312,64397376⟩ : DyadicInterval 40),(⟨-64401152,-64401088⟩ : DyadicInterval 40),(⟨762123381699,762123401029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168623860534,168748327412⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156880073664,156880073728⟩ : DyadicInterval 40),(⟨-183049627328,-183049627264⟩ : DyadicInterval 40),(⟨749141924682,749141944012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156987984896,156987984960⟩ : DyadicInterval 40),(⟨-183196650368,-183196650304⟩ : DyadicInterval 40),(⟨749122677122,749122696451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26208665472,-26169553600⟩ : DyadicInterval 40),(⟨775208160416,775227735616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1793_ok : ecellOkT e1793 = true := by decide +kernel
theorem e1793_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1793 e1793_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '1599/1600', '1999/2000']  interval_lower 72544617/549755813888
noncomputable def e1794 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267979440943,0,true,156744767552,156744767616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931043814609,0,false,-182865328512,-182865328448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268114406468,0,true,156861794880,156861794944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930908849084,0,false,-183024726976,-183024726912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554500173,0,true,42871552,42871616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468755379,0,false,-42873280,-42873216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565256456,0,true,53627328,53627392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457999096,0,false,-53630016,-53629952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625160,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626105,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268032115890,0,true,156790443008,156790443072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930991139662,0,false,-182927536512,-182927536448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268156582786,0,true,156898363008,156898363072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930866672766,0,false,-183074543232,-183074543168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073644579050,0,false,-26176180160,-26176180096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073682746847,0,false,-26137093504,-26137093440⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156744767552,156744767616⟩ : DyadicInterval 40),(⟨-182865328512,-182865328448⟩ : DyadicInterval 40),(⟨749166035492,749166054821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156861794880,156861794944⟩ : DyadicInterval 40),(⟨-183024726976,-183024726912⟩ : DyadicInterval 40),(⟨749145183390,749145202720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42872397,53628680⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42871552,42871616⟩ : DyadicInterval 40),(⟨-42873280,-42873216⟩ : DyadicInterval 40),(⟨762123382744,762123402073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53627328,53627392⟩ : DyadicInterval 40),(⟨-53630016,-53629952⟩ : DyadicInterval 40),(⟨762123382280,762123401609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168520488114,168644955010⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156790443008,156790443072⟩ : DyadicInterval 40),(⟨-182927536512,-182927536448⟩ : DyadicInterval 40),(⟨749157899246,749157918576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156898363008,156898363072⟩ : DyadicInterval 40),(⟨-183074543232,-183074543168⟩ : DyadicInterval 40),(⟨749138663686,749138683016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26176180160,-26137093440⟩ : DyadicInterval 40),(⟨775191930336,775211492960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1794_ok : ecellOkT e1794 = true := by decide +kernel
theorem e1794_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1794 e1794_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '1599/1600', '1999/2000']  interval_lower 73052307/549755813888
noncomputable def e1795 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268093320575,0,true,156843512320,156843512384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930929934977,0,false,-182999822336,-182999822272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268228300343,0,true,156960541504,156960541568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930794955209,0,false,-183159257088,-183159257024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554530162,0,true,42901504,42901568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468725390,0,false,-42903232,-42903168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565293946,0,true,53664832,53664896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457961606,0,false,-53667520,-53667456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625156,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626102,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268146031126,0,true,156889214528,156889214592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930877224426,0,false,-183062080000,-183062079936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268270505152,0,true,156997131072,156997131136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930752750400,0,false,-183209113088,-183209113024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073609620035,0,false,-26211982016,-26211981952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073647815812,0,false,-26172865408,-26172865344⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156843512320,156843512384⟩ : DyadicInterval 40),(⟨-182999822336,-182999822272⟩ : DyadicInterval 40),(⟨749148442259,749148461589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156960541504,156960541568⟩ : DyadicInterval 40),(⟨-183159257088,-183159257024⟩ : DyadicInterval 40),(⟨749127573615,749127592944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42902386,53666170⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42901504,42901568⟩ : DyadicInterval 40),(⟨-42903232,-42903168⟩ : DyadicInterval 40),(⟨762123382741,762123402071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53664832,53664896⟩ : DyadicInterval 40),(⟨-53667520,-53667456⟩ : DyadicInterval 40),(⟨762123382276,762123401605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168634403350,168758877376⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156889214528,156889214592⟩ : DyadicInterval 40),(⟨-183062080000,-183062079936⟩ : DyadicInterval 40),(⟨749140294932,749140314262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156997131072,156997131136⟩ : DyadicInterval 40),(⟨-183209113088,-183209113024⟩ : DyadicInterval 40),(⟨749121045011,749121064340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26211982016,-26172865344⟩ : DyadicInterval 40),(⟨775209816288,775229393888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1795_ok : ecellOkT e1795 = true := by decide +kernel
theorem e1795_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1795 e1795_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '3997/4000', '1599/1600']  interval_lower 73634993/549755813888
noncomputable def e1796 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268186100073,0,true,156923954688,156923954752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930837155479,0,false,-183109408704,-183109408640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268321079841,0,true,157040975296,157040975360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930702175711,0,false,-183268859328,-183268859264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565293196,0,true,53664064,53664128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457962356,0,false,-53666752,-53666688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576071977,0,true,64442304,64442368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447183575,0,false,-64446144,-64446080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623998,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625157,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268249396425,0,true,156978830976,156978831040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930773859127,0,false,-183184177344,-183184177280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268373870426,0,true,157086738688,157086738752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930649385126,0,false,-183331226752,-183331226688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073577880217,0,false,-26244488064,-26244488000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073616099390,0,false,-26205346368,-26205346304⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156923954688,156923954752⟩ : DyadicInterval 40),(⟨-183109408704,-183109408640⟩ : DyadicInterval 40),(⟨749134099835,749134119165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157040975296,157040975360⟩ : DyadicInterval 40),(⟨-183268859328,-183268859264⟩ : DyadicInterval 40),(⟨749113219526,749113238856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53665420,64444201⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53664064,53664128⟩ : DyadicInterval 40),(⟨-53666752,-53666688⟩ : DyadicInterval 40),(⟨762123382276,762123401605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64442304,64442368⟩ : DyadicInterval 40),(⟨-64446144,-64446080⟩ : DyadicInterval 40),(⟨762123381694,762123401023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168737768649,168862242650⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156978830976,156978831040⟩ : DyadicInterval 40),(⟨-183184177344,-183184177280⟩ : DyadicInterval 40),(⟨749124310491,749124329821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157086738688,157086738752⟩ : DyadicInterval 40),(⟨-183331226752,-183331226688⟩ : DyadicInterval 40),(⟨749105048607,749105067936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26244488064,-26205346304⟩ : DyadicInterval 40),(⟨775226056768,775245646912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1796_ok : ecellOkT e1796 = true := by decide +kernel
theorem e1796_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1796 e1796_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '3997/4000', '1599/1600']  interval_lower 74145469/549755813888
noncomputable def e1797 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268299965461,0,true,157022671040,157022671104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930723290091,0,false,-183243915584,-183243915520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268434959472,0,true,157139693504,157139693568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930588296080,0,false,-183403402560,-183403402496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565330686,0,true,53701568,53701632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457924866,0,false,-53704256,-53704192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576116970,0,true,64487296,64487360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447138582,0,false,-64491136,-64491072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623993,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625154,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268363304538,0,true,157077579392,157077579456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930659951014,0,false,-183318743808,-183318743744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268487785670,0,true,157185483648,157185483712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930535469882,0,false,-183465819712,-183465819648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073542878364,0,false,-26280336000,-26280335936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073581125520,0,false,-26241164352,-26241164288⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157022671040,157022671104⟩ : DyadicInterval 40),(⟨-183243915584,-183243915520⟩ : DyadicInterval 40),(⟨749116486883,749116506213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157139693504,157139693568⟩ : DyadicInterval 40),(⟨-183403402560,-183403402496⟩ : DyadicInterval 40),(⟨749095590050,749095609380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53702910,64489194⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53701568,53701632⟩ : DyadicInterval 40),(⟨-53704256,-53704192⟩ : DyadicInterval 40),(⟨762123382272,762123401602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64487296,64487360⟩ : DyadicInterval 40),(⟨-64491136,-64491072⟩ : DyadicInterval 40),(⟨762123381689,762123401018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168851676762,168976157894⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157077579392,157077579456⟩ : DyadicInterval 40),(⟨-183318743808,-183318743744⟩ : DyadicInterval 40),(⟨749106684222,749106703552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157185483648,157185483712⟩ : DyadicInterval 40),(⟨-183465819712,-183465819648⟩ : DyadicInterval 40),(⟨749087408026,749087427355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26280336000,-26241164288⟩ : DyadicInterval 40),(⟨775243965760,775263570880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1797_ok : ecellOkT e1797 = true := by decide +kernel
theorem e1797_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1797 e1797_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '1599/1600', '1999/2000']  interval_lower 147122695/1099511627776
noncomputable def e1798 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268207200207,0,true,156942248256,156942248320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930816055345,0,false,-183134332608,-183134332544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268342194219,0,true,157059279296,157059279360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930681061333,0,false,-183293803712,-183293803648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554560154,0,true,42931520,42931584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468695398,0,false,-42933248,-42933184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565331437,0,true,53702336,53702400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457924115,0,false,-53705024,-53704960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625152,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626100,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268259946368,0,true,156987977216,156987977280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930763309184,0,false,-183196639936,-183196639872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268384427514,0,true,157095890240,157095890304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930638828038,0,false,-183343699456,-183343699392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073574637415,0,false,-26247809216,-26247809152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073612861171,0,false,-26208662656,-26208662592⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156942248256,156942248320⟩ : DyadicInterval 40),(⟨-183134332608,-183134332544⟩ : DyadicInterval 40),(⟨749130836925,749130856255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157059279296,157059279360⟩ : DyadicInterval 40),(⟨-183293803712,-183293803648⟩ : DyadicInterval 40),(⟨749109951757,749109971086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42932378,53703661⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42931520,42931584⟩ : DyadicInterval 40),(⟨-42933248,-42933184⟩ : DyadicInterval 40),(⟨762123382739,762123402068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53702336,53702400⟩ : DyadicInterval 40),(⟨-53705024,-53704960⟩ : DyadicInterval 40),(⟨762123382272,762123401602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168748318592,168872799738⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156987977216,156987977280⟩ : DyadicInterval 40),(⟨-183196639936,-183196639872⟩ : DyadicInterval 40),(⟨749122678500,749122697830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157095890240,157095890304⟩ : DyadicInterval 40),(⟨-183343699456,-183343699392⟩ : DyadicInterval 40),(⟨749103414279,749103433608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26247809216,-26208662592⟩ : DyadicInterval 40),(⟨775227714912,775247307488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1798_ok : ecellOkT e1798 = true := by decide +kernel
theorem e1798_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1798 e1798_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '1599/1600', '1999/2000']  interval_lower 37035863/274877906944
noncomputable def e1799 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268321079838,0,true,157040975296,157040975360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930702175714,0,false,-183268859328,-183268859264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268456088094,0,true,157158008192,157158008256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930567167458,0,false,-183428366784,-183428366720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554590147,0,true,42961472,42961536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468665405,0,false,-42963264,-42963200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565368931,0,true,53739840,53739904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457886621,0,false,-53742528,-53742464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625149,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626098,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268373861603,0,true,157086731008,157086731072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930649393949,0,false,-183331216384,-183331216320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268498349881,0,true,157194640512,157194640576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930524905671,0,false,-183478302336,-183478302272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073539631185,0,false,-26283661760,-26283661696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073577882928,0,false,-26244485312,-26244485248⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157040975296,157040975360⟩ : DyadicInterval 40),(⟨-183268859328,-183268859264⟩ : DyadicInterval 40),(⟨749113219526,749113238856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157158008192,157158008256⟩ : DyadicInterval 40),(⟨-183428366784,-183428366720⟩ : DyadicInterval 40),(⟨749092317826,749092337155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42962371,53741155⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42961472,42961536⟩ : DyadicInterval 40),(⟨-42963264,-42963200⟩ : DyadicInterval 40),(⟨762123382769,762123402098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53739840,53739904⟩ : DyadicInterval 40),(⟨-53742528,-53742464⟩ : DyadicInterval 40),(⟨762123382269,762123401598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168862233827,168986722105⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157086731008,157086731072⟩ : DyadicInterval 40),(⟨-183331216384,-183331216320⟩ : DyadicInterval 40),(⟨749105050014,749105069344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157194640512,157194640576⟩ : DyadicInterval 40),(⟨-183478302336,-183478302272⟩ : DyadicInterval 40),(⟨749085771487,749085790816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26283661760,-26244485248⟩ : DyadicInterval 40),(⟨775245626240,775265233760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1799_ok : ecellOkT e1799 = true := by decide +kernel
theorem e1799_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1799 e1799_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B029

end


