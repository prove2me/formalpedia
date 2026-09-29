-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B008
-- name    : CK_CKLaneC2R_EpCells_B008
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:25:50.459864+00:00
-- url     : https://prove2.me/theorems/ee8e46b8-31f0-4de2-aa24-420e6d674ce1
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B008` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B008` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B008` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B008 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B008.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B008 =====
section

namespace CKLaneC2R.EpCells.B008

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['66417/256000', '106437/409600', '1999/2000', '1']  interval_lower 1624235985/1099511627776
noncomputable def e480 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1384770470674,0,true,253622471680,253622471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨814252784878,0,false,-330238890432,-330238890368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1385226274079,0,true,253984321344,253984321408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨813796981473,0,false,-330854548672,-330854548608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1384627841252,0,true,253509217728,253509217792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨814395414300,0,false,-330046310208,-330046310144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586758573,0,true,75128192,75128256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436496979,0,false,-75133376,-75133312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622642,0,false,-5184,-5120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1384699149874,0,true,253565841344,253565841408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨814324105678,0,false,-330142587904,-330142587840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1385226282707,0,true,253984328192,253984328256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨813796972845,0,false,-330854560320,-330854560256⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1025266970438,0,false,-76870232128,-76870232064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1025540674941,0,false,-76576746496,-76576746432⟩
    { al := (66417/256000), au := (106437/409600), zl := (1999/2000), zu := 1,
      A := ⟨285258842898,285714646303⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253622471680,253622471744⟩ : DyadicInterval 40),(⟨-330238890432,-330238890368⟩ : DyadicInterval 40),(⟨724692686507,724692705836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253984321344,253984321408⟩ : DyadicInterval 40),(⟨-330854548672,-330854548608⟩ : DyadicInterval 40),(⟨724571565077,724571584406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253509217728,253509217792⟩ : DyadicInterval 40),(⟨-330046310208,-330046310144⟩ : DyadicInterval 40),(⟨724730546012,724730565341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253984321344,253984321408⟩ : DyadicInterval 40),(⟨-330854548672,-330854548608⟩ : DyadicInterval 40),(⟨724571565077,724571584406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75130797⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75128192,75128256⟩ : DyadicInterval 40),(⟨-75133376,-75133312⟩ : DyadicInterval 40),(⟨762123381010,762123400339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,0⟩ : DyadicInterval 40),(⟨762123383616,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨285187522098,285714654931⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253565841344,253565841408⟩ : DyadicInterval 40),(⟨-330142587904,-330142587840⟩ : DyadicInterval 40),(⟨724711620353,724711639682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253984328192,253984328256⟩ : DyadicInterval 40),(⟨-330854560320,-330854560256⟩ : DyadicInterval 40),(⟨724571562779,724571582108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76870232128,-76576746432⟩ : DyadicInterval 40),(⟨800411756832,800558518944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨253622471680,253984321408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-330854548672,-330238890368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e480_ok : ecellOkT e480 = true := by decide +kernel
theorem e480_pos {a z : ℝ} (ha1 : ((66417/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((106437/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e480 e480_ok ha1 ha2 hz1 hz2 hz

-- box ['106437/409600', '266517/1024000', '1999/2000', '1']  interval_lower 823279861/549755813888
noncomputable def e481 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1385226274078,0,true,253984321344,253984321408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨813796981474,0,false,-330854548672,-330854548608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1385682077484,0,true,254346051904,254346051968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨813341178068,0,false,-331470551872,-331470551808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1385083416754,0,true,253870923712,253870923776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨813939838798,0,false,-330661552768,-330661552704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586891032,0,true,75260672,75260736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436364520,0,false,-75265856,-75265792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622624,0,false,-5184,-5120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1385154839328,0,true,253927619136,253927619200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨813868416224,0,false,-330758038272,-330758038208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1385682086107,0,true,254346058752,254346058816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨813341169445,0,false,-331470563584,-331470563520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1025029895020,0,false,-77124504768,-77124504704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1025304095774,0,false,-76830419072,-76830419008⟩
    { al := (106437/409600), au := (266517/1024000), zl := (1999/2000), zu := 1,
      A := ⟨285714646302,286170449708⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253984321344,253984321408⟩ : DyadicInterval 40),(⟨-330854548672,-330854548608⟩ : DyadicInterval 40),(⟨724571565077,724571584406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254346051904,254346051968⟩ : DyadicInterval 40),(⟨-331470551872,-331470551808⟩ : DyadicInterval 40),(⟨724450241060,724450260390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253870923712,253870923776⟩ : DyadicInterval 40),(⟨-330661552768,-330661552704⟩ : DyadicInterval 40),(⟨724609548596,724609567925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254346051904,254346051968⟩ : DyadicInterval 40),(⟨-331470551872,-331470551808⟩ : DyadicInterval 40),(⟨724450241060,724450260390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75263256⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75260672,75260736⟩ : DyadicInterval 40),(⟨-75265856,-75265792⟩ : DyadicInterval 40),(⟨762123380991,762123400321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,0⟩ : DyadicInterval 40),(⟨762123383616,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨285643211552,286170458331⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253927619136,253927619200⟩ : DyadicInterval 40),(⟨-330758038272,-330758038208⟩ : DyadicInterval 40),(⟨724590560961,724590580290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254346058752,254346058816⟩ : DyadicInterval 40),(⟨-331470563584,-331470563520⟩ : DyadicInterval 40),(⟨724450238779,724450258109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77124504768,-76830419008⟩ : DyadicInterval 40),(⟨800538593120,800685655264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨253984321344,254346051968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-331470551872,-330854548608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e481_ok : ecellOkT e481 = true := by decide +kernel
theorem e481_pos {a z : ℝ} (ha1 : ((106437/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((266517/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e481 e481_ok ha1 ha2 hz1 hz2 hz

-- box ['266517/1024000', '533883/2048000', '999/1000', '1999/2000']  interval_lower 1674411607/1099511627776
noncomputable def e482 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1385682077483,0,true,254346051904,254346051968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨813341178069,0,false,-331470551872,-331470551808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1386137880888,0,true,254707663552,254707663616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨812885374664,0,false,-332086900416,-332086900352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1385395907033,0,true,254118957824,254118957888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨813627348519,0,false,-331083761664,-331083761600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1385994567762,0,true,254593978880,254593978944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨813028687790,0,false,-331893071680,-331893071616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586886558,0,true,75256192,75256256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436368994,0,false,-75261376,-75261312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099662415098,0,true,150776960,150777024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099360840454,0,false,-150797696,-150797632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607096,0,false,-20736,-20672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622625,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1385538988841,0,true,254232508032,254232508096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨813484266711,0,false,-331277135168,-331277135104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1386066233844,0,true,254650830208,254650830272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨812957021708,0,false,-331989994624,-331989994560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1024829796147,0,false,-77339164352,-77339164288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1025104364396,0,false,-77044627136,-77044627072⟩
    { al := (266517/1024000), au := (533883/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨286170449707,286626253112⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254346051904,254346051968⟩ : DyadicInterval 40),(⟨-331470551872,-331470551808⟩ : DyadicInterval 40),(⟨724450241061,724450260390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254707663552,254707663616⟩ : DyadicInterval 40),(⟨-332086900416,-332086900352⟩ : DyadicInterval 40),(⟨724328714338,724328733667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254118957824,254118957888⟩ : DyadicInterval 40),(⟨-331083761664,-331083761600⟩ : DyadicInterval 40),(⟨724526436488,724526455818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254593978880,254593978944⟩ : DyadicInterval 40),(⟨-331893071680,-331893071616⟩ : DyadicInterval 40),(⟨724366946484,724366965813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75258782,150787322⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75256192,75256256⟩ : DyadicInterval 40),(⟨-75261376,-75261312⟩ : DyadicInterval 40),(⟨762123380992,762123400321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨150776960,150777024⟩ : DyadicInterval 40),(⟨-150797696,-150797632⟩ : DyadicInterval 40),(⟨762123373240,762123392570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20736,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123413248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨286027361065,286554606068⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254232508032,254232508096⟩ : DyadicInterval 40),(⟨-331277135168,-331277135104⟩ : DyadicInterval 40),(⟨724488349670,724488368999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254650830208,254650830272⟩ : DyadicInterval 40),(⟨-331989994624,-331989994560⟩ : DyadicInterval 40),(⟨724347830384,724347849714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77339164352,-77044627072⟩ : DyadicInterval 40),(⟨800645697152,800792985056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨254346051904,254707663616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-332086900416,-331470551808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e482_ok : ecellOkT e482 = true := by decide +kernel
theorem e482_pos {a z : ℝ} (ha1 : ((266517/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((533883/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e482 e482_ok ha1 ha2 hz1 hz2 hz

-- box ['533883/2048000', '133683/512000', '999/1000', '1999/2000']  interval_lower 26516525/17179869184
noncomputable def e483 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1386137880887,0,true,254707663552,254707663616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨812885374665,0,false,-332086900416,-332086900352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1386593684292,0,true,255069156288,255069156352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨812429571260,0,false,-332703594624,-332703594560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1385851254633,0,true,254480282496,254480282560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨813172000919,0,false,-331699277056,-331699276992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1386450143264,0,true,254955328256,254955328320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨812573112288,0,false,-332509348736,-332509348672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587019061,0,true,75388672,75388736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436236491,0,false,-75393920,-75393856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099662680258,0,true,151042048,151042112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099360575294,0,false,-151062912,-151062848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607024,0,false,-20800,-20736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622607,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1385994564351,0,true,254593976192,254593976256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨813028691201,0,false,-331893067008,-331893066944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1386521923307,0,true,255012251264,255012251328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨812501332245,0,false,-332606480256,-332606480192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1024592083807,0,false,-77594228992,-77594228928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1024867148468,0,false,-77299090816,-77299090752⟩
    { al := (533883/2048000), au := (133683/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨286626253111,287082056516⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254707663552,254707663616⟩ : DyadicInterval 40),(⟨-332086900416,-332086900352⟩ : DyadicInterval 40),(⟨724328714338,724328733667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255069156288,255069156352⟩ : DyadicInterval 40),(⟨-332703594624,-332703594560⟩ : DyadicInterval 40),(⟨724206984887,724207004216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254480282496,254480282560⟩ : DyadicInterval 40),(⟨-331699277056,-331699276992⟩ : DyadicInterval 40),(⟨724405158544,724405177873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254955328256,254955328320⟩ : DyadicInterval 40),(⟨-332509348736,-332509348672⟩ : DyadicInterval 40),(⟨724245341648,724245360978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75391285,151052482⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75388672,75388736⟩ : DyadicInterval 40),(⟨-75393920,-75393856⟩ : DyadicInterval 40),(⟨762123381006,762123400335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨151042048,151042112⟩ : DyadicInterval 40),(⟨-151062912,-151062848⟩ : DyadicInterval 40),(⟨762123373231,762123392561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20800,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123413280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨286482936575,287010295531⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254593976192,254593976256⟩ : DyadicInterval 40),(⟨-331893067008,-331893066944⟩ : DyadicInterval 40),(⟨724366947360,724366966690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255012251264,255012251328⟩ : DyadicInterval 40),(⟨-332606480256,-332606480192⟩ : DyadicInterval 40),(⟨724226163248,724226182577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77594228992,-77299090752⟩ : DyadicInterval 40),(⟨800772928992,800920517376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨254707663552,255069156352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-332703594624,-332086900352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e483_ok : ecellOkT e483 = true := by decide +kernel
theorem e483_pos {a z : ℝ} (ha1 : ((533883/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133683/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e483 e483_ok ha1 ha2 hz1 hz2 hz

-- box ['266517/1024000', '533883/2048000', '1999/2000', '1']  interval_lower 1669027687/1099511627776
noncomputable def e484 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1385682077483,0,true,254346051904,254346051968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨813341178069,0,false,-331470551872,-331470551808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1386137880888,0,true,254707663552,254707663616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨812885374664,0,false,-332086900416,-332086900352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1385538992258,0,true,254232510720,254232510784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨813484263294,0,false,-331277139776,-331277139712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587023557,0,true,75393152,75393216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436231995,0,false,-75398400,-75398336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622605,0,false,-5184,-5120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1385610528773,0,true,254289277952,254289278016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨813412726779,0,false,-331373833344,-331373833280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1386137889515,0,true,254707670400,254707670464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨812885366037,0,false,-332086912064,-332086912000⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1024792441690,0,false,-77379241664,-77379241600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1025067138893,0,false,-77084555392,-77084555328⟩
    { al := (266517/1024000), au := (533883/2048000), zl := (1999/2000), zu := 1,
      A := ⟨286170449707,286626253112⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254346051904,254346051968⟩ : DyadicInterval 40),(⟨-331470551872,-331470551808⟩ : DyadicInterval 40),(⟨724450241061,724450260390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254707663552,254707663616⟩ : DyadicInterval 40),(⟨-332086900416,-332086900352⟩ : DyadicInterval 40),(⟨724328714338,724328733667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254232510720,254232510784⟩ : DyadicInterval 40),(⟨-331277139776,-331277139712⟩ : DyadicInterval 40),(⟨724488348771,724488368100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254707663552,254707663616⟩ : DyadicInterval 40),(⟨-332086900416,-332086900352⟩ : DyadicInterval 40),(⟨724328714338,724328733667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75395781⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75393152,75393216⟩ : DyadicInterval 40),(⟨-75398400,-75398336⟩ : DyadicInterval 40),(⟨762123381005,762123400335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,0⟩ : DyadicInterval 40),(⟨762123383616,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨286098900997,286626261739⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254289277952,254289278016⟩ : DyadicInterval 40),(⟨-331373833344,-331373833280⟩ : DyadicInterval 40),(⟨724469299034,724469318363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254707670400,254707670464⟩ : DyadicInterval 40),(⟨-332086912064,-332086912000⟩ : DyadicInterval 40),(⟨724328712025,724328731354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77379241664,-77084555328⟩ : DyadicInterval 40),(⟨800665661280,800813023712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨254346051904,254707663616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-332086900416,-331470551808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e484_ok : ecellOkT e484 = true := by decide +kernel
theorem e484_pos {a z : ℝ} (ha1 : ((266517/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((533883/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e484 e484_ok ha1 ha2 hz1 hz2 hz

-- box ['533883/2048000', '133683/512000', '1999/2000', '1']  interval_lower 105727499/68719476736
noncomputable def e485 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1386137880887,0,true,254707663552,254707663616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨812885374665,0,false,-332086900416,-332086900352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1386593684292,0,true,255069156288,255069156352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨812429571260,0,false,-332703594624,-332703594560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1385994567760,0,true,254593978880,254593978944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨813028687792,0,false,-331893071616,-331893071552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587156147,0,true,75525760,75525824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436099405,0,false,-75531008,-75530944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622587,0,false,-5248,-5184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1386066218224,0,true,254650817856,254650817920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨812957037328,0,false,-331989973504,-331989973440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1386593692921,0,true,255069163072,255069163136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨812429562631,0,false,-332703606272,-332703606208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1024554610454,0,false,-77634443136,-77634443072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1024829804290,0,false,-77339155648,-77339155584⟩
    { al := (533883/2048000), au := (133683/512000), zl := (1999/2000), zu := 1,
      A := ⟨286626253111,287082056516⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254707663552,254707663616⟩ : DyadicInterval 40),(⟨-332086900416,-332086900352⟩ : DyadicInterval 40),(⟨724328714338,724328733667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255069156288,255069156352⟩ : DyadicInterval 40),(⟨-332703594624,-332703594560⟩ : DyadicInterval 40),(⟨724206984887,724207004216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254593978880,254593978944⟩ : DyadicInterval 40),(⟨-331893071616,-331893071552⟩ : DyadicInterval 40),(⟨724366946461,724366965790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255069156288,255069156352⟩ : DyadicInterval 40),(⟨-332703594624,-332703594560⟩ : DyadicInterval 40),(⟨724206984887,724207004216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75528371⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75525760,75525824⟩ : DyadicInterval 40),(⟨-75531008,-75530944⟩ : DyadicInterval 40),(⟨762123380987,762123400316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,0⟩ : DyadicInterval 40),(⟨762123383616,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨286554590448,287082065145⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254650817856,254650817920⟩ : DyadicInterval 40),(⟨-331989973504,-331989973440⟩ : DyadicInterval 40),(⟨724347834529,724347853858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255069163072,255069163136⟩ : DyadicInterval 40),(⟨-332703606272,-332703606208⟩ : DyadicInterval 40),(⟨724206982606,724207001936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77634443136,-77339155584⟩ : DyadicInterval 40),(⟨800792961408,800940624448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨254707663552,255069156352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-332703594624,-332086900352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e485_ok : ecellOkT e485 = true := by decide +kernel
theorem e485_pos {a z : ℝ} (ha1 : ((533883/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133683/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e485 e485_ok ha1 ha2 hz1 hz2 hz

-- box ['133683/512000', '535581/2048000', '999/1000', '1999/2000']  interval_lower 1719848991/1099511627776
noncomputable def e486 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1386593684291,0,true,255069156288,255069156352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨812429571261,0,false,-332703594624,-332703594560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1387049487696,0,true,255430530176,255430530240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨811973767856,0,false,-333320634880,-333320634816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1386306602234,0,true,254841488448,254841488512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨812716653318,0,false,-332315137152,-332315137088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1386905718767,0,true,255316558912,255316558976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨812117536785,0,false,-333125971456,-333125971392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587151631,0,true,75521216,75521280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436103921,0,false,-75526464,-75526400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099662945548,0,true,151307328,151307392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099360310004,0,false,-151328192,-151328128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606951,0,false,-20864,-20800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622589,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1386450139861,0,true,254955325568,254955325632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨812573115691,0,false,-332509344128,-332509344064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1386977612765,0,true,255373553600,255373553664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨812045642787,0,false,-333223311808,-333223311744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1024353993751,0,false,-77849758208,-77849758144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1024629555011,0,false,-77554018560,-77554018496⟩
    { al := (133683/512000), au := (535581/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨287082056515,287537859920⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255069156288,255069156352⟩ : DyadicInterval 40),(⟨-332703594624,-332703594560⟩ : DyadicInterval 40),(⟨724206984887,724207004217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255430530176,255430530240⟩ : DyadicInterval 40),(⟨-333320634880,-333320634816⟩ : DyadicInterval 40),(⟨724085052668,724085071997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254841488448,254841488512⟩ : DyadicInterval 40),(⟨-332315137152,-332315137088⟩ : DyadicInterval 40),(⟨724283678293,724283697623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255316558912,255316558976⟩ : DyadicInterval 40),(⟨-333125971456,-333125971392⟩ : DyadicInterval 40),(⟨724123534272,724123553601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75523855,151317772⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75521216,75521280⟩ : DyadicInterval 40),(⟨-75526464,-75526400⟩ : DyadicInterval 40),(⟨762123380988,762123400317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨151307328,151307392⟩ : DyadicInterval 40),(⟨-151328192,-151328128⟩ : DyadicInterval 40),(⟨762123373158,762123392488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20864,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123413312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨286938512085,287465984989⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254955325568,254955325632⟩ : DyadicInterval 40),(⟨-332509344128,-332509344064⟩ : DyadicInterval 40),(⟨724245342550,724245361879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255373553600,255373553664⟩ : DyadicInterval 40),(⟨-333223311808,-333223311744⟩ : DyadicInterval 40),(⟨724104293441,724104312771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77849758208,-77554018496⟩ : DyadicInterval 40),(⟨800900392864,801048281984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨255069156288,255430530240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-333320634880,-332703594560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e486_ok : ecellOkT e486 = true := by decide +kernel
theorem e486_pos {a z : ℝ} (ha1 : ((133683/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((535581/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e486 e486_ok ha1 ha2 hz1 hz2 hz

-- box ['535581/2048000', '53643/204800', '999/1000', '1999/2000']  interval_lower 217848325/137438953472
noncomputable def e487 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1387049487695,0,true,255430530176,255430530240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨811973767857,0,false,-333320634880,-333320634816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1387505291101,0,true,255791785344,255791785408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨811517964451,0,false,-333938021696,-333938021632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1386761949835,0,true,255202575808,255202575872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨812261305717,0,false,-332931342464,-332931342400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1387361294270,0,true,255677670912,255677670976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨811661961282,0,false,-333742940160,-333742940096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587284265,0,true,75653824,75653888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435971287,0,false,-75659136,-75659072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099663210970,0,true,151572736,151572800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099360044582,0,false,-151593664,-151593600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606878,0,false,-20928,-20864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622571,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1386905715370,0,true,255316556224,255316556288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨812117540182,0,false,-333125966848,-333125966784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1387433302219,0,true,255734737152,255734737216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨811589953333,0,false,-333840489536,-333840489472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1024115525979,0,false,-78105752320,-78105752256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1024391584025,0,false,-77809410624,-77809410560⟩
    { al := (535581/2048000), au := (53643/204800), zl := (999/1000), zu := (1999/2000),
      A := ⟨287537859919,287993663325⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255430530176,255430530240⟩ : DyadicInterval 40),(⟨-333320634880,-333320634816⟩ : DyadicInterval 40),(⟨724085052668,724085071997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255791785344,255791785408⟩ : DyadicInterval 40),(⟨-333938021696,-333938021632⟩ : DyadicInterval 40),(⟨723962917647,723962936977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255202575808,255202575872⟩ : DyadicInterval 40),(⟨-332931342464,-332931342400⟩ : DyadicInterval 40),(⟨724161995705,724162015035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255677670912,255677670976⟩ : DyadicInterval 40),(⟨-333742940160,-333742940096⟩ : DyadicInterval 40),(⟨724001524291,724001543620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75656489,151583194⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75653824,75653888⟩ : DyadicInterval 40),(⟨-75659136,-75659072⟩ : DyadicInterval 40),(⟨762123381001,762123400331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨151572736,151572800⟩ : DyadicInterval 40),(⟨-151593664,-151593600⟩ : DyadicInterval 40),(⟨762123373117,762123392447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20928,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123413344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨287394087594,287921674443⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255316556224,255316556288⟩ : DyadicInterval 40),(⟨-333125966848,-333125966784⟩ : DyadicInterval 40),(⟨724123535174,724123554504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255734737152,255734737216⟩ : DyadicInterval 40),(⟨-333840489536,-333840489472⟩ : DyadicInterval 40),(⟨723982220958,723982240288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78105752320,-77809410560⟩ : DyadicInterval 40),(⟨801028088896,801176279040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨255430530176,255791785408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-333938021696,-333320634816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e487_ok : ecellOkT e487 = true := by decide +kernel
theorem e487_pos {a z : ℝ} (ha1 : ((535581/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53643/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e487 e487_ok ha1 ha2 hz1 hz2 hz

-- box ['133683/512000', '535581/2048000', '1999/2000', '1']  interval_lower 857198933/549755813888
noncomputable def e488 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1386593684291,0,true,255069156288,255069156352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨812429571261,0,false,-332703594624,-332703594560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1387049487696,0,true,255430530176,255430530240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨811973767856,0,false,-333320634880,-333320634816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1386450143262,0,true,254955328256,254955328320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨812573112290,0,false,-332509348736,-332509348672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587288801,0,true,75658368,75658432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435966751,0,false,-75663680,-75663616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622569,0,false,-5248,-5184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1386521907672,0,true,255012238912,255012238976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨812501347880,0,false,-332606459136,-332606459072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1387049496324,0,true,255430537024,255430537088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨811973759228,0,false,-333320646592,-333320646528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1024316401313,0,false,-77890109568,-77890109504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1024592091971,0,false,-77594220224,-77594220160⟩
    { al := (133683/512000), au := (535581/2048000), zl := (1999/2000), zu := 1,
      A := ⟨287082056515,287537859920⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255069156288,255069156352⟩ : DyadicInterval 40),(⟨-332703594624,-332703594560⟩ : DyadicInterval 40),(⟨724206984887,724207004217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255430530176,255430530240⟩ : DyadicInterval 40),(⟨-333320634880,-333320634816⟩ : DyadicInterval 40),(⟨724085052668,724085071997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254955328256,254955328320⟩ : DyadicInterval 40),(⟨-332509348736,-332509348672⟩ : DyadicInterval 40),(⟨724245341649,724245360978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255430530176,255430530240⟩ : DyadicInterval 40),(⟨-333320634880,-333320634816⟩ : DyadicInterval 40),(⟨724085052668,724085071997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75661025⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75658368,75658432⟩ : DyadicInterval 40),(⟨-75663680,-75663616⟩ : DyadicInterval 40),(⟨762123381001,762123400330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,0⟩ : DyadicInterval 40),(⟨762123383616,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨287010279896,287537868548⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255012238912,255012238976⟩ : DyadicInterval 40),(⟨-332606459136,-332606459072⟩ : DyadicInterval 40),(⟨724226167410,724226186740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255430537024,255430537088⟩ : DyadicInterval 40),(⟨-333320646592,-333320646528⟩ : DyadicInterval 40),(⟨724085050363,724085069693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77890109568,-77594220160⟩ : DyadicInterval 40),(⟨800920493696,801068457664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨255069156288,255430530240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-333320634880,-332703594560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e488_ok : ecellOkT e488 = true := by decide +kernel
theorem e488_pos {a z : ℝ} (ha1 : ((133683/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((535581/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e488 e488_ok ha1 ha2 hz1 hz2 hz

-- box ['535581/2048000', '53643/204800', '1999/2000', '1']  interval_lower 1737301455/1099511627776
noncomputable def e489 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1387049487695,0,true,255430530176,255430530240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨811973767857,0,false,-333320634880,-333320634816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1387505291101,0,true,255791785344,255791785408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨811517964451,0,false,-333938021696,-333938021632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1386905718765,0,true,255316558912,255316558976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨812117536787,0,false,-333125971456,-333125971392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587421523,0,true,75791104,75791168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435834029,0,false,-75796416,-75796352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622551,0,false,-5248,-5184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1386977597121,0,true,255373541184,255373541248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨812045658431,0,false,-333223290624,-333223290560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1387505299720,0,true,255791792192,255791792256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨811517955832,0,false,-333938033344,-333938033280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1024077814267,0,false,-78146241152,-78146241088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1024354001933,0,false,-77849749376,-77849749312⟩
    { al := (535581/2048000), au := (53643/204800), zl := (1999/2000), zu := 1,
      A := ⟨287537859919,287993663325⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255430530176,255430530240⟩ : DyadicInterval 40),(⟨-333320634880,-333320634816⟩ : DyadicInterval 40),(⟨724085052668,724085071997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255791785344,255791785408⟩ : DyadicInterval 40),(⟨-333938021696,-333938021632⟩ : DyadicInterval 40),(⟨723962917647,723962936977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255316558912,255316558976⟩ : DyadicInterval 40),(⟨-333125971456,-333125971392⟩ : DyadicInterval 40),(⟨724123534272,724123553602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255791785344,255791785408⟩ : DyadicInterval 40),(⟨-333938021696,-333938021632⟩ : DyadicInterval 40),(⟨723962917647,723962936977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75793747⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75791104,75791168⟩ : DyadicInterval 40),(⟨-75796416,-75796352⟩ : DyadicInterval 40),(⟨762123380983,762123400312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,0⟩ : DyadicInterval 40),(⟨762123383616,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨287465969345,287993671944⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255373541184,255373541248⟩ : DyadicInterval 40),(⟨-333223290624,-333223290560⟩ : DyadicInterval 40),(⟨724104297637,724104316966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255791792192,255791792256⟩ : DyadicInterval 40),(⟨-333938033344,-333938033280⟩ : DyadicInterval 40),(⟨723962915313,723962934643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78146241152,-77849749312⟩ : DyadicInterval 40),(⟨801048258272,801196523456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨255430530176,255791785408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-333938021696,-333320634816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e489_ok : ecellOkT e489 = true := by decide +kernel
theorem e489_pos {a z : ℝ} (ha1 : ((535581/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53643/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e489 e489_ok ha1 ha2 hz1 hz2 hz

-- box ['53643/204800', '537279/2048000', '999/1000', '1999/2000']  interval_lower 1765871151/1099511627776
noncomputable def e490 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1387505291100,0,true,255791785344,255791785408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨811517964452,0,false,-333938021696,-333938021632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1387961094505,0,true,256152921856,256152921920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨811062161047,0,false,-334555755328,-334555755264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1387217297436,0,true,255563544576,255563544640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨811805958116,0,false,-333547893248,-333547893184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1387816869772,0,true,256038664320,256038664384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨811206385780,0,false,-334360255296,-334360255232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587416966,0,true,75786560,75786624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435838586,0,false,-75791808,-75791744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099663476524,0,true,151838208,151838272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099359779028,0,false,-151859264,-151859200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606804,0,false,-20992,-20928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622552,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1387361290874,0,true,255677668224,255677668288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨811661964678,0,false,-333742935552,-333742935488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1387888991668,0,true,256095802176,256095802240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨811134263884,0,false,-334458013888,-334458013824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1023876680491,0,false,-78362211648,-78362211584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1024153235512,0,false,-78065267328,-78065267264⟩
    { al := (53643/204800), au := (537279/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨287993663324,288449466729⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255791785344,255791785408⟩ : DyadicInterval 40),(⟨-333938021696,-333938021632⟩ : DyadicInterval 40),(⟨723962917647,723962936977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256152921856,256152921920⟩ : DyadicInterval 40),(⟨-334555755328,-334555755264⟩ : DyadicInterval 40),(⟨723840579738,723840599068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255563544576,255563544640⟩ : DyadicInterval 40),(⟨-333547893248,-333547893184⟩ : DyadicInterval 40),(⟨724040110733,724040130063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256038664320,256038664384⟩ : DyadicInterval 40),(⟨-334360255296,-334360255232⟩ : DyadicInterval 40),(⟨723879311690,723879331020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75789190,151848748⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75786560,75786624⟩ : DyadicInterval 40),(⟨-75791808,-75791744⟩ : DyadicInterval 40),(⟨762123380951,762123400281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨151838208,151838272⟩ : DyadicInterval 40),(⟨-151859264,-151859200⟩ : DyadicInterval 40),(⟨762123373108,762123392438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20992,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123413376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨287849663098,288377363892⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255677668224,255677668288⟩ : DyadicInterval 40),(⟨-333742935552,-333742935488⟩ : DyadicInterval 40),(⟨724001525196,724001544526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256095802176,256095802240⟩ : DyadicInterval 40),(⟨-334458013888,-334458013824⟩ : DyadicInterval 40),(⟨723859945662,723859964991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78362211648,-78065267264⟩ : DyadicInterval 40),(⟨801156017248,801304508704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨255791785344,256152921920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-334555755328,-333938021632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e490_ok : ecellOkT e490 = true := by decide +kernel
theorem e490_pos {a z : ℝ} (ha1 : ((53643/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((537279/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e490 e490_ok ha1 ha2 hz1 hz2 hz

-- box ['537279/2048000', '33633/128000', '999/1000', '1999/2000']  interval_lower 894551423/549755813888
noncomputable def e491 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1387961094504,0,true,256152921856,256152921920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨811062161048,0,false,-334555755328,-334555755264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1388416897909,0,true,256513939840,256513939904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨810606357643,0,false,-335173836160,-335173836096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1387672645037,0,true,255924394944,255924395008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨811350610515,0,false,-334164790016,-334164789952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1388272445275,0,true,256399539328,256399539392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨810750810277,0,false,-334977917184,-334977917120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587549733,0,true,75919296,75919360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435705819,0,false,-75924608,-75924544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099663742212,0,true,152103872,152103936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099359513340,0,false,-152124992,-152124928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606731,0,false,-21056,-20992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622534,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1387816866384,0,true,256038661696,256038661760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨811206389168,0,false,-334360250688,-334360250624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1388344681139,0,true,256456748608,256456748672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨810678574413,0,false,-335075885248,-335075885184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1023637457273,0,false,-78619136576,-78619136512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1023914509466,0,false,-78321588992,-78321588928⟩
    { al := (537279/2048000), au := (33633/128000), zl := (999/1000), zu := (1999/2000),
      A := ⟨288449466728,288905270133⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256152921856,256152921920⟩ : DyadicInterval 40),(⟨-334555755328,-334555755264⟩ : DyadicInterval 40),(⟨723840579738,723840599068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256513939840,256513939904⟩ : DyadicInterval 40),(⟨-335173836160,-335173836096⟩ : DyadicInterval 40),(⟨723718038859,723718058188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255924394944,255924395008⟩ : DyadicInterval 40),(⟨-334164790016,-334164789952⟩ : DyadicInterval 40),(⟨723918023304,723918042634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256399539328,256399539392⟩ : DyadicInterval 40),(⟨-334977917184,-334977917120⟩ : DyadicInterval 40),(⟨723756896323,723756915652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75921957,152114436⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75919296,75919360⟩ : DyadicInterval 40),(⟨-75924608,-75924544⟩ : DyadicInterval 40),(⟨762123380965,762123400294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨152103872,152103936⟩ : DyadicInterval 40),(⟨-152124992,-152124928⟩ : DyadicInterval 40),(⟨762123373066,762123392396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21056,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123413408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨288305238608,288833053363⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256038661696,256038661760⟩ : DyadicInterval 40),(⟨-334360250688,-334360250624⟩ : DyadicInterval 40),(⟨723879312556,723879331885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256456748608,256456748672⟩ : DyadicInterval 40),(⟨-335075885248,-335075885184⟩ : DyadicInterval 40),(⟨723737467583,723737486913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78619136576,-78321588928⟩ : DyadicInterval 40),(⟨801284178080,801432971168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨256152921856,256513939904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-335173836160,-334555755264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e491_ok : ecellOkT e491 = true := by decide +kernel
theorem e491_pos {a z : ℝ} (ha1 : ((537279/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33633/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e491 e491_ok ha1 ha2 hz1 hz2 hz

-- box ['53643/204800', '537279/2048000', '1999/2000', '1']  interval_lower 1760351647/1099511627776
noncomputable def e492 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1387505291100,0,true,255791785344,255791785408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨811517964452,0,false,-333938021696,-333938021632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1387961094505,0,true,256152921856,256152921920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨811062161047,0,false,-334555755328,-334555755264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1387361294268,0,true,255677670912,255677670976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨811661961284,0,false,-333742940160,-333742940096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587554311,0,true,75923904,75923968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435701241,0,false,-75929216,-75929152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622532,0,false,-5248,-5184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1387433286565,0,true,255734724736,255734724800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨811589968987,0,false,-333840468288,-333840468224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1387961103121,0,true,256152928704,256152928768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨811062152431,0,false,-334555766976,-334555766912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1023838849312,0,false,-78402838272,-78402838208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1024115534179,0,false,-78105743488,-78105743424⟩
    { al := (53643/204800), au := (537279/2048000), zl := (1999/2000), zu := 1,
      A := ⟨287993663324,288449466729⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255791785344,255791785408⟩ : DyadicInterval 40),(⟨-333938021696,-333938021632⟩ : DyadicInterval 40),(⟨723962917647,723962936977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256152921856,256152921920⟩ : DyadicInterval 40),(⟨-334555755328,-334555755264⟩ : DyadicInterval 40),(⟨723840579738,723840599068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255677670912,255677670976⟩ : DyadicInterval 40),(⟨-333742940160,-333742940096⟩ : DyadicInterval 40),(⟨724001524292,724001543621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256152921856,256152921920⟩ : DyadicInterval 40),(⟨-334555755328,-334555755264⟩ : DyadicInterval 40),(⟨723840579738,723840599068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,75926535⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75923904,75923968⟩ : DyadicInterval 40),(⟨-75929216,-75929152⟩ : DyadicInterval 40),(⟨762123380964,762123400294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,0⟩ : DyadicInterval 40),(⟨762123383616,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨287921658789,288449475345⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨255734724736,255734724800⟩ : DyadicInterval 40),(⟨-333840468288,-333840468224⟩ : DyadicInterval 40),(⟨723982225147,723982244476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256152928704,256152928768⟩ : DyadicInterval 40),(⟨-334555766976,-334555766912⟩ : DyadicInterval 40),(⟨723840577397,723840596727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78402838272,-78105743424⟩ : DyadicInterval 40),(⟨801176255328,801324822016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨255791785344,256152921920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-334555755328,-333938021632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e492_ok : ecellOkT e492 = true := by decide +kernel
theorem e492_pos {a z : ℝ} (ha1 : ((53643/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((537279/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e492 e492_ok ha1 ha2 hz1 hz2 hz

-- box ['537279/2048000', '33633/128000', '1999/2000', '1']  interval_lower 1783549181/1099511627776
noncomputable def e493 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1387961094504,0,true,256152921856,256152921920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨811062161048,0,false,-334555755328,-334555755264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1388416897909,0,true,256513939840,256513939904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨810606357643,0,false,-335173836160,-335173836096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1387816869770,0,true,256038664320,256038664384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨811206385782,0,false,-334360255296,-334360255232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587687165,0,true,76056704,76056768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435568387,0,false,-76062080,-76062016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622514,0,false,-5312,-5248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1387888976005,0,true,256095789760,256095789824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨811134279547,0,false,-334457992640,-334457992576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1388416906540,0,true,256513946688,256513946752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨810606349012,0,false,-335173847872,-335173847808⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1023599506440,0,false,-78659901184,-78659901120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1023876688708,0,false,-78362202880,-78362202816⟩
    { al := (537279/2048000), au := (33633/128000), zl := (1999/2000), zu := 1,
      A := ⟨288449466728,288905270133⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256152921856,256152921920⟩ : DyadicInterval 40),(⟨-334555755328,-334555755264⟩ : DyadicInterval 40),(⟨723840579738,723840599068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256513939840,256513939904⟩ : DyadicInterval 40),(⟨-335173836160,-335173836096⟩ : DyadicInterval 40),(⟨723718038859,723718058188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256038664320,256038664384⟩ : DyadicInterval 40),(⟨-334360255296,-334360255232⟩ : DyadicInterval 40),(⟨723879311690,723879331020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256513939840,256513939904⟩ : DyadicInterval 40),(⟨-335173836160,-335173836096⟩ : DyadicInterval 40),(⟨723718038859,723718058188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76059389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76056704,76056768⟩ : DyadicInterval 40),(⟨-76062080,-76062016⟩ : DyadicInterval 40),(⟨762123380978,762123400307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,0⟩ : DyadicInterval 40),(⟨762123383616,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨288377348229,288905278764⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256095789760,256095789824⟩ : DyadicInterval 40),(⟨-334457992640,-334457992576⟩ : DyadicInterval 40),(⟨723859949866,723859969196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256513946688,256513946752⟩ : DyadicInterval 40),(⟨-335173847872,-335173847808⟩ : DyadicInterval 40),(⟨723718036530,723718055859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78659901184,-78362202816⟩ : DyadicInterval 40),(⟨801304485024,801453353472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨256152921856,256513939904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-335173836160,-334555755264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e493_ok : ecellOkT e493 = true := by decide +kernel
theorem e493_pos {a z : ℝ} (ha1 : ((537279/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33633/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e493 e493_ok ha1 ha2 hz1 hz2 hz

-- box ['33633/128000', '538977/2048000', '999/1000', '1999/2000']  interval_lower 906241373/549755813888
noncomputable def e494 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1388416897908,0,true,256513939840,256513939904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨810606357644,0,false,-335173836160,-335173836096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1388872701314,0,true,256874839296,256874839360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨810150554238,0,false,-335792264704,-335792264640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1388127992637,0,true,256285126912,256285126976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨810895262915,0,false,-334782033024,-334782032960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1388728020778,0,true,256760295872,256760295936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨810295234774,0,false,-335595926208,-335595926144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587682565,0,true,76052096,76052160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435572987,0,false,-76057472,-76057408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099664008030,0,true,152369664,152369728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099359247522,0,false,-152390848,-152390784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606657,0,false,-21120,-21056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622516,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1388272441906,0,true,256399536640,256399536704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨810750813646,0,false,-334977912576,-334977912512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1388800370599,0,true,256817576640,256817576704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨810222884953,0,false,-335694104064,-335694104000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1023397856343,0,false,-78876527360,-78876527296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1023675405884,0,false,-78578375936,-78578375872⟩
    { al := (33633/128000), au := (538977/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨288905270132,289361073538⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256513939840,256513939904⟩ : DyadicInterval 40),(⟨-335173836160,-335173836096⟩ : DyadicInterval 40),(⟨723718038859,723718058189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256874839296,256874839360⟩ : DyadicInterval 40),(⟨-335792264704,-335792264640⟩ : DyadicInterval 40),(⟨723595295055,723595314385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256285126912,256285126976⟩ : DyadicInterval 40),(⟨-334782033024,-334782032960⟩ : DyadicInterval 40),(⟨723795733372,723795752702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256760295872,256760295936⟩ : DyadicInterval 40),(⟨-335595926208,-335595926144⟩ : DyadicInterval 40),(⟨723634278231,723634297561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76054789,152380254⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76052096,76052160⟩ : DyadicInterval 40),(⟨-76057472,-76057408⟩ : DyadicInterval 40),(⟨762123380979,762123400308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨152369664,152369728⟩ : DyadicInterval 40),(⟨-152390848,-152390784⟩ : DyadicInterval 40),(⟨762123373025,762123392355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21120,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123413440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨288760814130,289288742823⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256399536640,256399536704⟩ : DyadicInterval 40),(⟨-334977912576,-334977912512⟩ : DyadicInterval 40),(⟨723756897227,723756916557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256817576640,256817576704⟩ : DyadicInterval 40),(⟨-335694104064,-335694104000⟩ : DyadicInterval 40),(⟨723614786635,723614805964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78876527360,-78578375872⟩ : DyadicInterval 40),(⟨801412571552,801561666560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨256513939840,256874839360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-335792264704,-335173836096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e494_ok : ecellOkT e494 = true := by decide +kernel
theorem e494_pos {a z : ℝ} (ha1 : ((33633/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((538977/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e494 e494_ok ha1 ha2 hz1 hz2 hz

-- box ['538977/2048000', '269913/1024000', '999/1000', '1999/2000']  interval_lower 918005631/549755813888
noncomputable def e495 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1388872701313,0,true,256874839296,256874839360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨810150554239,0,false,-335792264704,-335792264640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1389328504718,0,true,257235620288,257235620352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨809694750834,0,false,-336411041280,-336411041216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1388583340239,0,true,256645740544,256645740608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨810439915313,0,false,-335399622784,-335399622720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1389183596280,0,true,257120934080,257120934144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨809839659272,0,false,-336214282880,-336214282816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587815465,0,true,76185024,76185088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435440087,0,false,-76190336,-76190272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099664273982,0,true,152635584,152635648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099358981570,0,false,-152656832,-152656768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606583,0,false,-21248,-21184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622497,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1388728017418,0,true,256760293248,256760293312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨810295238134,0,false,-335595921664,-335595921600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1389256060046,0,true,257178286272,257178286336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨809767195506,0,false,-336312670656,-336312670592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1023157877701,0,false,-79134384320,-79134384256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1023435924778,0,false,-78835628416,-78835628352⟩
    { al := (538977/2048000), au := (269913/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨289361073537,289816876942⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256874839296,256874839360⟩ : DyadicInterval 40),(⟨-335792264704,-335792264640⟩ : DyadicInterval 40),(⟨723595295056,723595314385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257235620288,257235620352⟩ : DyadicInterval 40),(⟨-336411041280,-336411041216⟩ : DyadicInterval 40),(⟨723472348264,723472367594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256645740544,256645740608⟩ : DyadicInterval 40),(⟨-335399622784,-335399622720⟩ : DyadicInterval 40),(⟨723673240942,723673260271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257120934080,257120934144⟩ : DyadicInterval 40),(⟨-336214282880,-336214282816⟩ : DyadicInterval 40),(⟨723511457379,723511476709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76187689,152646206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76185024,76185088⟩ : DyadicInterval 40),(⟨-76190336,-76190272⟩ : DyadicInterval 40),(⟨762123380928,762123400257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨152635584,152635648⟩ : DyadicInterval 40),(⟨-152656832,-152656768⟩ : DyadicInterval 40),(⟨762123372983,762123392313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21248,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123413504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨289216389642,289744432270⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256760293248,256760293312⟩ : DyadicInterval 40),(⟨-335595921664,-335595921600⟩ : DyadicInterval 40),(⟨723634279119,723634298448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257178286272,257178286336⟩ : DyadicInterval 40),(⟨-336312670656,-336312670592⟩ : DyadicInterval 40),(⟨723491902792,723491922122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79134384320,-78835628352⟩ : DyadicInterval 40),(⟨801541197792,801690595040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨256874839296,257235620352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-336411041280,-335792264640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e495_ok : ecellOkT e495 = true := by decide +kernel
theorem e495_pos {a z : ℝ} (ha1 : ((538977/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((269913/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e495 e495_ok ha1 ha2 hz1 hz2 hz

-- box ['33633/128000', '538977/2048000', '1999/2000', '1']  interval_lower 1806894431/1099511627776
noncomputable def e496 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1388416897908,0,true,256513939840,256513939904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨810606357644,0,false,-335173836160,-335173836096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1388872701314,0,true,256874839296,256874839360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨810150554238,0,false,-335792264704,-335792264640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1388272445272,0,true,256399539328,256399539392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨810750810280,0,false,-334977917184,-334977917120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587820085,0,true,76189632,76189696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435435467,0,false,-76195008,-76194944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622496,0,false,-5312,-5248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1388344665465,0,true,256456736192,256456736256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨810678590087,0,false,-335075864000,-335075863936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1388872709944,0,true,256874846144,256874846208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨810150545608,0,false,-335792276416,-335792276352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1023359785668,0,false,-78917430272,-78917430208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1023637465509,0,false,-78619127744,-78619127680⟩
    { al := (33633/128000), au := (538977/2048000), zl := (1999/2000), zu := 1,
      A := ⟨288905270132,289361073538⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256513939840,256513939904⟩ : DyadicInterval 40),(⟨-335173836160,-335173836096⟩ : DyadicInterval 40),(⟨723718038859,723718058189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256874839296,256874839360⟩ : DyadicInterval 40),(⟨-335792264704,-335792264640⟩ : DyadicInterval 40),(⟨723595295055,723595314385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256399539328,256399539392⟩ : DyadicInterval 40),(⟨-334977917184,-334977917120⟩ : DyadicInterval 40),(⟨723756896324,723756915653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256874839296,256874839360⟩ : DyadicInterval 40),(⟨-335792264704,-335792264640⟩ : DyadicInterval 40),(⟨723595295055,723595314385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76192309⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76189632,76189696⟩ : DyadicInterval 40),(⟨-76195008,-76194944⟩ : DyadicInterval 40),(⟨762123380959,762123400289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,0⟩ : DyadicInterval 40),(⟨762123383616,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨288833037689,289361082168⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256456736192,256456736256⟩ : DyadicInterval 40),(⟨-335075864000,-335075863936⟩ : DyadicInterval 40),(⟨723737471805,723737491135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256874846144,256874846208⟩ : DyadicInterval 40),(⟨-335792276416,-335792276352⟩ : DyadicInterval 40),(⟨723595292719,723595312049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-78917430272,-78619127680⟩ : DyadicInterval 40),(⟨801432947456,801582118016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨256513939840,256874839360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-335792264704,-335173836096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e496_ok : ecellOkT e496 = true := by decide +kernel
theorem e496_pos {a z : ℝ} (ha1 : ((33633/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((538977/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e496 e496_ok ha1 ha2 hz1 hz2 hz

-- box ['538977/2048000', '269913/1024000', '1999/2000', '1']  interval_lower 457597143/274877906944
noncomputable def e497 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1388872701313,0,true,256874839296,256874839360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨810150554239,0,false,-335792264704,-335792264640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1389328504718,0,true,257235620288,257235620352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨809694750834,0,false,-336411041280,-336411041216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1388728020776,0,true,256760295872,256760295936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨810295234776,0,false,-335595926208,-335595926144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587953072,0,true,76322624,76322688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435302480,0,false,-76328000,-76327936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622477,0,false,-5312,-5248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1388800354915,0,true,256817564224,256817564288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨810222900637,0,false,-335694082752,-335694082688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1389328513338,0,true,257235627136,257235627200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨809694742214,0,false,-336411052992,-336411052928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1023119686995,0,false,-79175425792,-79175425728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1023397864597,0,false,-78876518528,-78876518464⟩
    { al := (538977/2048000), au := (269913/1024000), zl := (1999/2000), zu := 1,
      A := ⟨289361073537,289816876942⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256874839296,256874839360⟩ : DyadicInterval 40),(⟨-335792264704,-335792264640⟩ : DyadicInterval 40),(⟨723595295056,723595314385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257235620288,257235620352⟩ : DyadicInterval 40),(⟨-336411041280,-336411041216⟩ : DyadicInterval 40),(⟨723472348264,723472367594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256760295872,256760295936⟩ : DyadicInterval 40),(⟨-335595926208,-335595926144⟩ : DyadicInterval 40),(⟨723634278231,723634297561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257235620288,257235620352⟩ : DyadicInterval 40),(⟨-336411041280,-336411041216⟩ : DyadicInterval 40),(⟨723472348264,723472367594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76325296⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76322624,76322688⟩ : DyadicInterval 40),(⟨-76328000,-76327936⟩ : DyadicInterval 40),(⟨762123380941,762123400270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,0⟩ : DyadicInterval 40),(⟨762123383616,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨289288727139,289816885562⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨256817564224,256817564288⟩ : DyadicInterval 40),(⟨-335694082752,-335694082688⟩ : DyadicInterval 40),(⟨723614790850,723614810180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257235627136,257235627200⟩ : DyadicInterval 40),(⟨-336411052992,-336411052928⟩ : DyadicInterval 40),(⟨723472345923,723472365252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79175425792,-78876518464⟩ : DyadicInterval 40),(⟨801561642848,801711115776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨256874839296,257235620352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-336411041280,-335792264640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e497_ok : ecellOkT e497 = true := by decide +kernel
theorem e497_pos {a z : ℝ} (ha1 : ((538977/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((269913/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e497 e497_ok ha1 ha2 hz1 hz2 hz

-- box ['269913/1024000', '21627/81920', '999/1000', '1999/2000']  interval_lower 1859688973/1099511627776
noncomputable def e498 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1389328504717,0,true,257235620288,257235620352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨809694750835,0,false,-336411041280,-336411041216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1389784308122,0,true,257596283008,257596283072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨809238947430,0,false,-337030166272,-337030166208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1389038687839,0,true,257006235904,257006235968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨809984567713,0,false,-336017559616,-336017559552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1389639171783,0,true,257481454080,257481454144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨809384083769,0,false,-336832987456,-336832987392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587948430,0,true,76317952,76318016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435307122,0,false,-76323328,-76323264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099664540068,0,true,152901632,152901696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099358715484,0,false,-152922944,-152922880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606510,0,false,-21312,-21248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622479,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1389183592919,0,true,257120931456,257120931520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨809839662633,0,false,-336214278272,-336214278208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1389711749511,0,true,257538877632,257538877696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨809311506041,0,false,-336931585408,-336931585344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1022917521331,0,false,-79392707776,-79392707712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1023196066149,0,false,-79093346816,-79093346752⟩
    { al := (269913/1024000), au := (21627/81920), zl := (999/1000), zu := (1999/2000),
      A := ⟨289816876941,290272680346⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257235620288,257235620352⟩ : DyadicInterval 40),(⟨-336411041280,-336411041216⟩ : DyadicInterval 40),(⟨723472348264,723472367594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257596283008,257596283072⟩ : DyadicInterval 40),(⟨-337030166272,-337030166208⟩ : DyadicInterval 40),(⟨723349198361,723349217690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257006235904,257006235968⟩ : DyadicInterval 40),(⟨-336017559616,-336017559552⟩ : DyadicInterval 40),(⟨723550545950,723550565280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257481454080,257481454144⟩ : DyadicInterval 40),(⟨-336832987456,-336832987392⟩ : DyadicInterval 40),(⟨723388433638,723388452967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76320654,152912292⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76317952,76318016⟩ : DyadicInterval 40),(⟨-76323328,-76323264⟩ : DyadicInterval 40),(⟨762123380942,762123400271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨152901632,152901696⟩ : DyadicInterval 40),(⟨-152922944,-152922880⟩ : DyadicInterval 40),(⟨762123372941,762123392271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21312,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123413536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨289671965143,290200121735⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257120931456,257120931520⟩ : DyadicInterval 40),(⟨-336214278272,-336214278208⟩ : DyadicInterval 40),(⟨723511458246,723511477576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257538877632,257538877696⟩ : DyadicInterval 40),(⟨-336931585408,-336931585344⟩ : DyadicInterval 40),(⟨723368815965,723368835294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79392707776,-79093346752⟩ : DyadicInterval 40),(⟨801670056992,801819756768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨257235620288,257596283072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-337030166272,-336411041216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e498_ok : ecellOkT e498 = true := by decide +kernel
theorem e498_pos {a z : ℝ} (ha1 : ((269913/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21627/81920 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e498 e498_ok ha1 ha2 hz1 hz2 hz

-- box ['21627/81920', '135381/512000', '999/1000', '1999/2000']  interval_lower 1883516945/1099511627776
noncomputable def e499 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1389784308121,0,true,257596283008,257596283072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨809238947431,0,false,-337030166272,-337030166208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1390240111526,0,true,257956827456,257956827520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨808783144026,0,false,-337649640064,-337649640000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1389494035440,0,true,257366613184,257366613248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨809529220112,0,false,-336635843968,-336635843904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1390094747285,0,true,257841855872,257841855936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨808928508267,0,false,-337452040384,-337452040320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588081462,0,true,76451008,76451072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435174090,0,false,-76456384,-76456320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099664806286,0,true,153167808,153167872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099358449266,0,false,-153189184,-153189120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606435,0,false,-21376,-21312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622460,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1389639168435,0,true,257481451456,257481451520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨809384087117,0,false,-336832982912,-336832982848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1390167438972,0,true,257899350720,257899350784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨808855816580,0,false,-337550848768,-337550848704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1022676787245,0,false,-79651498048,-79651497984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1022955829982,0,false,-79351531456,-79351531392⟩
    { al := (21627/81920), au := (135381/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨290272680345,290728483750⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257596283008,257596283072⟩ : DyadicInterval 40),(⟨-337030166272,-337030166208⟩ : DyadicInterval 40),(⟨723349198361,723349217690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257956827456,257956827520⟩ : DyadicInterval 40),(⟨-337649640064,-337649640000⟩ : DyadicInterval 40),(⟨723225845344,723225864674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257366613184,257366613248⟩ : DyadicInterval 40),(⟨-336635843968,-336635843904⟩ : DyadicInterval 40),(⟨723427648298,723427667628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257841855872,257841855936⟩ : DyadicInterval 40),(⟨-337452040384,-337452040320⟩ : DyadicInterval 40),(⟨723265207030,723265226359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76453686,153178510⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76451008,76451072⟩ : DyadicInterval 40),(⟨-76456384,-76456320⟩ : DyadicInterval 40),(⟨762123380923,762123400253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153167808,153167872⟩ : DyadicInterval 40),(⟨-153189184,-153189120⟩ : DyadicInterval 40),(⟨762123372899,762123392229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21376,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123413568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨290127540659,290655811196⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257481451456,257481451520⟩ : DyadicInterval 40),(⟨-336832982912,-336832982848⟩ : DyadicInterval 40),(⟨723388434529,723388453858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257899350720,257899350784⟩ : DyadicInterval 40),(⟨-337550848768,-337550848704⟩ : DyadicInterval 40),(⟨723245526180,723245545510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79651498048,-79351531392⟩ : DyadicInterval 40),(⟨801799149312,801949151904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨257596283008,257956827520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-337649640064,-337030166208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e499_ok : ecellOkT e499 = true := by decide +kernel
theorem e499_pos {a z : ℝ} (ha1 : ((21627/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((135381/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e499 e499_ok ha1 ha2 hz1 hz2 hz

-- box ['269913/1024000', '21627/81920', '1999/2000', '1']  interval_lower 28969237/17179869184
noncomputable def e500 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1389328504717,0,true,257235620288,257235620352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨809694750835,0,false,-336411041280,-336411041216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1389784308122,0,true,257596283008,257596283072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨809238947430,0,false,-337030166272,-337030166208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1389183596278,0,true,257120934080,257120934144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨809839659274,0,false,-336214282880,-336214282816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588086126,0,true,76455680,76455744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435169426,0,false,-76461056,-76460992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622459,0,false,-5376,-5312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1389256044352,0,true,257178273856,257178273920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨809767211200,0,false,-336312649344,-336312649280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1389784316751,0,true,257596289856,257596289920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨809238938801,0,false,-337030177984,-337030177920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1022879210404,0,false,-79433888128,-79433888064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1023157885973,0,false,-79134375424,-79134375360⟩
    { al := (269913/1024000), au := (21627/81920), zl := (1999/2000), zu := 1,
      A := ⟨289816876941,290272680346⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257235620288,257235620352⟩ : DyadicInterval 40),(⟨-336411041280,-336411041216⟩ : DyadicInterval 40),(⟨723472348264,723472367594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257596283008,257596283072⟩ : DyadicInterval 40),(⟨-337030166272,-337030166208⟩ : DyadicInterval 40),(⟨723349198361,723349217690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257120934080,257120934144⟩ : DyadicInterval 40),(⟨-336214282880,-336214282816⟩ : DyadicInterval 40),(⟨723511457380,723511476709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257596283008,257596283072⟩ : DyadicInterval 40),(⟨-337030166272,-337030166208⟩ : DyadicInterval 40),(⟨723349198361,723349217690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76458350⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76455680,76455744⟩ : DyadicInterval 40),(⟨-76461056,-76460992⟩ : DyadicInterval 40),(⟨762123380923,762123400252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,0⟩ : DyadicInterval 40),(⟨762123383616,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨289744416576,290272688975⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257178273856,257178273920⟩ : DyadicInterval 40),(⟨-336312649344,-336312649280⟩ : DyadicInterval 40),(⟨723491907024,723491926353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257596289856,257596289920⟩ : DyadicInterval 40),(⟨-337030177984,-337030177920⟩ : DyadicInterval 40),(⟨723349196010,723349215339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79433888128,-79134375360⟩ : DyadicInterval 40),(⟨801690571296,801840346944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨257235620288,257596283072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-337030166272,-336411041216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e500_ok : ecellOkT e500 = true := by decide +kernel
theorem e500_pos {a z : ℝ} (ha1 : ((269913/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21627/81920 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e500 e500_ok ha1 ha2 hz1 hz2 hz

-- box ['21627/81920', '135381/512000', '1999/2000', '1']  interval_lower 1877824129/1099511627776
noncomputable def e501 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1389784308121,0,true,257596283008,257596283072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨809238947431,0,false,-337030166272,-337030166208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1390240111526,0,true,257956827456,257956827520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨808783144026,0,false,-337649640064,-337649640000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1389639171780,0,true,257481454080,257481454144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨809384083772,0,false,-336832987456,-336832987392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588219244,0,true,76588800,76588864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435036308,0,false,-76594176,-76594112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622440,0,false,-5376,-5312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1389711733807,0,true,257538865216,257538865280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨809311521745,0,false,-336931564096,-336931564032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1390240120164,0,true,257956834240,257956834304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨808783135388,0,false,-337649651840,-337649651776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1022638355906,0,false,-79692817536,-79692817472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1022917529622,0,false,-79392698880,-79392698816⟩
    { al := (21627/81920), au := (135381/512000), zl := (1999/2000), zu := 1,
      A := ⟨290272680345,290728483750⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257596283008,257596283072⟩ : DyadicInterval 40),(⟨-337030166272,-337030166208⟩ : DyadicInterval 40),(⟨723349198361,723349217690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257956827456,257956827520⟩ : DyadicInterval 40),(⟨-337649640064,-337649640000⟩ : DyadicInterval 40),(⟨723225845344,723225864674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257481454080,257481454144⟩ : DyadicInterval 40),(⟨-336832987456,-336832987392⟩ : DyadicInterval 40),(⟨723388433639,723388452968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257956827456,257956827520⟩ : DyadicInterval 40),(⟨-337649640064,-337649640000⟩ : DyadicInterval 40),(⟨723225845344,723225864674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76591468⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76588800,76588864⟩ : DyadicInterval 40),(⟨-76594176,-76594112⟩ : DyadicInterval 40),(⟨762123380904,762123400233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,0⟩ : DyadicInterval 40),(⟨762123383616,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨290200106031,290728492388⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257538865216,257538865280⟩ : DyadicInterval 40),(⟨-336931564096,-336931564032⟩ : DyadicInterval 40),(⟨723368820213,723368839543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257956834240,257956834304⟩ : DyadicInterval 40),(⟨-337649651840,-337649651776⟩ : DyadicInterval 40),(⟨723225843047,723225862376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79692817536,-79392698816⟩ : DyadicInterval 40),(⟨801819733024,801969811648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨257596283008,257956827520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-337649640064,-337030166208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e501_ok : ecellOkT e501 = true := by decide +kernel
theorem e501_pos {a z : ℝ} (ha1 : ((21627/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((135381/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e501 e501_ok ha1 ha2 hz1 hz2 hz

-- box ['135381/512000', '542373/2048000', '999/1000', '1999/2000']  interval_lower 238436945/137438953472
noncomputable def e502 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1390240111525,0,true,257956827456,257956827520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨808783144027,0,false,-337649640064,-337649640000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1390695914931,0,true,258317253632,258317253696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨808327340621,0,false,-338269463104,-338269463040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1389949383041,0,true,257726872320,257726872384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨809073872511,0,false,-337254476160,-337254476096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1390550322788,0,true,258202139584,258202139648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨808472932764,0,false,-338071442048,-338071441984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588214561,0,true,76584064,76584128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435040991,0,false,-76589504,-76589440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099665072640,0,true,153434112,153434176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099358182912,0,false,-153455616,-153455552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606361,0,false,-21440,-21376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622442,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1390094743948,0,true,257841853248,257841853312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨808928511604,0,false,-337452035840,-337452035776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1390623128423,0,true,258259705728,258259705792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨808400127129,0,false,-338170461120,-338170461056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1022435675445,0,false,-79910755392,-79910755328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1022715216287,0,false,-79610182528,-79610182464⟩
    { al := (135381/512000), au := (542373/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨290728483749,291184287155⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257956827456,257956827520⟩ : DyadicInterval 40),(⟨-337649640064,-337649640000⟩ : DyadicInterval 40),(⟨723225845345,723225864674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258317253632,258317253696⟩ : DyadicInterval 40),(⟨-338269463104,-338269463040⟩ : DyadicInterval 40),(⟨723102289235,723102308564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257726872320,257726872384⟩ : DyadicInterval 40),(⟨-337254476160,-337254476096⟩ : DyadicInterval 40),(⟨723304548002,723304567332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258202139584,258202139648⟩ : DyadicInterval 40),(⟨-338071442048,-338071441984⟩ : DyadicInterval 40),(⟨723141777472,723141796801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76586785,153444864⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76584064,76584128⟩ : DyadicInterval 40),(⟨-76589504,-76589440⟩ : DyadicInterval 40),(⟨762123380937,762123400266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153434112,153434176⟩ : DyadicInterval 40),(⟨-153455616,-153455552⟩ : DyadicInterval 40),(⟨762123372889,762123392219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21440,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123413600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨290583116172,291111500647⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257841853248,257841853312⟩ : DyadicInterval 40),(⟨-337452035840,-337452035776⟩ : DyadicInterval 40),(⟨723265207920,723265227250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258259705728,258259705792⟩ : DyadicInterval 40),(⟨-338170461120,-338170461056⟩ : DyadicInterval 40),(⟨723122033316,723122052646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79910755392,-79610182464⟩ : DyadicInterval 40),(⟨801928474848,802078780576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨257956827456,258317253696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-338269463104,-337649640000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e502_ok : ecellOkT e502 = true := by decide +kernel
theorem e502_pos {a z : ℝ} (ha1 : ((135381/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((542373/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e502 e502_ok ha1 ha2 hz1 hz2 hz

-- box ['542373/2048000', '271611/1024000', '999/1000', '1999/2000']  interval_lower 1931625313/1099511627776
noncomputable def e503 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1390695914930,0,true,258317253632,258317253696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨808327340622,0,false,-338269463104,-338269463040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1391151718335,0,true,258677561792,258677561856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨807871537217,0,false,-338889635712,-338889635648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1390404730642,0,true,258087013504,258087013568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨808618524910,0,false,-337873456640,-337873456576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1391005898290,0,true,258562305280,258562305344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨808017357262,0,false,-338691192832,-338691192768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588347727,0,true,76717248,76717312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434907825,0,false,-76722688,-76722624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099665339127,0,true,153700544,153700608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099357916425,0,false,-153722112,-153722048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606287,0,false,-21504,-21440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622423,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1390550319453,0,true,258202136960,258202137024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨808472936099,0,false,-338071437504,-338071437440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1391078817889,0,true,258619942656,258619942720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨807944437663,0,false,-338790422848,-338790422784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1022194185920,0,false,-80170480192,-80170480128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1022474225067,0,false,-79869300480,-79869300416⟩
    { al := (542373/2048000), au := (271611/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨291184287154,291640090559⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258317253632,258317253696⟩ : DyadicInterval 40),(⟨-338269463104,-338269463040⟩ : DyadicInterval 40),(⟨723102289236,723102308565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258677561792,258677561856⟩ : DyadicInterval 40),(⟨-338889635712,-338889635648⟩ : DyadicInterval 40),(⟨722978529846,722978549176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258087013504,258087013568⟩ : DyadicInterval 40),(⟨-337873456640,-337873456576⟩ : DyadicInterval 40),(⟨723181244962,723181264291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258562305280,258562305344⟩ : DyadicInterval 40),(⟨-338691192832,-338691192768⟩ : DyadicInterval 40),(⟨723018144922,723018164252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76719951,153711351⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76717248,76717312⟩ : DyadicInterval 40),(⟨-76722688,-76722624⟩ : DyadicInterval 40),(⟨762123380918,762123400247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153700544,153700608⟩ : DyadicInterval 40),(⟨-153722112,-153722048⟩ : DyadicInterval 40),(⟨762123372846,762123392176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21504,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123413632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨291038691677,291567190113⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258202136960,258202137024⟩ : DyadicInterval 40),(⟨-338071437504,-338071437440⟩ : DyadicInterval 40),(⟨723141778365,723141797695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258619942656,258619942720⟩ : DyadicInterval 40),(⟨-338790422848,-338790422784⟩ : DyadicInterval 40),(⟨722998337365,722998356694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80170480192,-79869300416⟩ : DyadicInterval 40),(⟨802058033824,802208642976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨258317253632,258677561856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-338889635712,-338269463040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e503_ok : ecellOkT e503 = true := by decide +kernel
theorem e503_pos {a z : ℝ} (ha1 : ((542373/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((271611/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e503 e503_ok ha1 ha2 hz1 hz2 hz

-- box ['135381/512000', '542373/2048000', '1999/2000', '1']  interval_lower 118860473/68719476736
noncomputable def e504 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1390240111525,0,true,257956827456,257956827520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨808783144027,0,false,-337649640064,-337649640000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1390695914931,0,true,258317253632,258317253696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨808327340621,0,false,-338269463104,-338269463040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1390094747283,0,true,257841855872,257841855936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨808928508269,0,false,-337452040384,-337452040320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588352432,0,true,76721920,76721984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434903120,0,false,-76727360,-76727296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622422,0,false,-5376,-5312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1390167423258,0,true,257899338304,257899338368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨808855832294,0,false,-337550827456,-337550827392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1390695923555,0,true,258317260480,258317260544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨808327331997,0,false,-338269474816,-338269474752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1022397123512,0,false,-79952214336,-79952214272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1022676795554,0,false,-79651489088,-79651489024⟩
    { al := (135381/512000), au := (542373/2048000), zl := (1999/2000), zu := 1,
      A := ⟨290728483749,291184287155⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257956827456,257956827520⟩ : DyadicInterval 40),(⟨-337649640064,-337649640000⟩ : DyadicInterval 40),(⟨723225845345,723225864674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258317253632,258317253696⟩ : DyadicInterval 40),(⟨-338269463104,-338269463040⟩ : DyadicInterval 40),(⟨723102289235,723102308564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257841855872,257841855936⟩ : DyadicInterval 40),(⟨-337452040384,-337452040320⟩ : DyadicInterval 40),(⟨723265207031,723265226360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258317253632,258317253696⟩ : DyadicInterval 40),(⟨-338269463104,-338269463040⟩ : DyadicInterval 40),(⟨723102289235,723102308564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76724656⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76721920,76721984⟩ : DyadicInterval 40),(⟨-76727360,-76727296⟩ : DyadicInterval 40),(⟨762123380917,762123400247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,0⟩ : DyadicInterval 40),(⟨762123383616,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨290655795482,291184295779⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨257899338304,257899338368⟩ : DyadicInterval 40),(⟨-337550827456,-337550827392⟩ : DyadicInterval 40),(⟨723245530445,723245549775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258317260480,258317260544⟩ : DyadicInterval 40),(⟨-338269474816,-338269474752⟩ : DyadicInterval 40),(⟨723102286870,723102306200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79952214336,-79651489024⟩ : DyadicInterval 40),(⟨801949128128,802099510048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨257956827456,258317253696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-338269463104,-337649640000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e504_ok : ecellOkT e504 = true := by decide +kernel
theorem e504_pos {a z : ℝ} (ha1 : ((135381/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((542373/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e504 e504_ok ha1 ha2 hz1 hz2 hz

-- box ['542373/2048000', '271611/1024000', '1999/2000', '1']  interval_lower 1925861833/1099511627776
noncomputable def e505 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1390695914930,0,true,258317253632,258317253696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨808327340622,0,false,-338269463104,-338269463040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1391151718335,0,true,258677561792,258677561856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨807871537217,0,false,-338889635712,-338889635648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1390550322786,0,true,258202139584,258202139648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨808472932766,0,false,-338071442048,-338071441984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588485686,0,true,76855168,76855232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434769866,0,false,-76860608,-76860544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622403,0,false,-5376,-5312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1390623112700,0,true,258259693248,258259693312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨808400142852,0,false,-338170439744,-338170439680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1391151726972,0,true,258677568576,258677568640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨807871528580,0,false,-338889647488,-338889647424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1022155513197,0,false,-80212078848,-80212078784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1022435683772,0,false,-79910746432,-79910746368⟩
    { al := (542373/2048000), au := (271611/1024000), zl := (1999/2000), zu := 1,
      A := ⟨291184287154,291640090559⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258317253632,258317253696⟩ : DyadicInterval 40),(⟨-338269463104,-338269463040⟩ : DyadicInterval 40),(⟨723102289236,723102308565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258677561792,258677561856⟩ : DyadicInterval 40),(⟨-338889635712,-338889635648⟩ : DyadicInterval 40),(⟨722978529846,722978549176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258202139584,258202139648⟩ : DyadicInterval 40),(⟨-338071442048,-338071441984⟩ : DyadicInterval 40),(⟨723141777473,723141796802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258677561792,258677561856⟩ : DyadicInterval 40),(⟨-338889635712,-338889635648⟩ : DyadicInterval 40),(⟨722978529846,722978549176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76857910⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76855168,76855232⟩ : DyadicInterval 40),(⟨-76860608,-76860544⟩ : DyadicInterval 40),(⟨762123380899,762123400228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,0⟩ : DyadicInterval 40),(⟨762123383616,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨291111484924,291640099196⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258259693248,258259693312⟩ : DyadicInterval 40),(⟨-338170439744,-338170439680⟩ : DyadicInterval 40),(⟨723122037615,723122056944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258677568576,258677568640⟩ : DyadicInterval 40),(⟨-338889647488,-338889647424⟩ : DyadicInterval 40),(⟨722978527534,722978546864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80212078848,-79910746368⟩ : DyadicInterval 40),(⟨802078756800,802229442304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨258317253632,258677561856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-338889635712,-338269463040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e505_ok : ecellOkT e505 = true := by decide +kernel
theorem e505_pos {a z : ℝ} (ha1 : ((542373/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((271611/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e505 e505_ok ha1 ha2 hz1 hz2 hz

-- box ['271611/1024000', '544071/2048000', '999/1000', '1999/2000']  interval_lower 488976795/274877906944
noncomputable def e506 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1391151718334,0,true,258677561792,258677561856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨807871537218,0,false,-338889635712,-338889635648⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1391607521739,0,true,259037751872,259037751936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨807415733813,0,false,-339510158400,-339510158336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1390860078243,0,true,258447036736,258447036800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨808163177309,0,false,-338492785728,-338492785664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1391461473793,0,true,258922353088,258922353152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨807561781759,0,false,-339311293184,-339311293120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588480959,0,true,76850496,76850560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434774593,0,false,-76855872,-76855808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099665605749,0,true,153967168,153967232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099357649803,0,false,-153988800,-153988736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606212,0,false,-21568,-21504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622405,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1391005894971,0,true,258562302656,258562302720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨808017360581,0,false,-338691188352,-338691188288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1391534507347,0,true,258980061568,258980061632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨807488748205,0,false,-339410734336,-339410734272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1021952318680,0,false,-80430672768,-80430672704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1022232856310,0,false,-80128885632,-80128885568⟩
    { al := (271611/1024000), au := (544071/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨291640090558,292095893963⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258677561792,258677561856⟩ : DyadicInterval 40),(⟨-338889635712,-338889635648⟩ : DyadicInterval 40),(⟨722978529847,722978549176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259037751872,259037751936⟩ : DyadicInterval 40),(⟨-339510158400,-339510158336⟩ : DyadicInterval 40),(⟨722854567262,722854586592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258447036736,258447036800⟩ : DyadicInterval 40),(⟨-338492785728,-338492785664⟩ : DyadicInterval 40),(⟨723057739152,723057758482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258922353088,258922353152⟩ : DyadicInterval 40),(⟨-339311293184,-339311293120⟩ : DyadicInterval 40),(⟨722894309319,722894328648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76853183,153977973⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76850496,76850560⟩ : DyadicInterval 40),(⟨-76855872,-76855808⟩ : DyadicInterval 40),(⟨762123380867,762123400197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967168,153967232⟩ : DyadicInterval 40),(⟨-153988800,-153988736⟩ : DyadicInterval 40),(⟨762123372804,762123392134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21568,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123413664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨291494267195,292022879571⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258562302656,258562302720⟩ : DyadicInterval 40),(⟨-338691188352,-338691188288⟩ : DyadicInterval 40),(⟨723018145837,723018165167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258980061568,258980061632⟩ : DyadicInterval 40),(⟨-339410734336,-339410734272⟩ : DyadicInterval 40),(⟨722874438288,722874457617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80430672768,-80128885568⟩ : DyadicInterval 40),(⟨802187826400,802338739264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨258677561792,259037751936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-339510158400,-338889635648⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e506_ok : ecellOkT e506 = true := by decide +kernel
theorem e506_pos {a z : ℝ} (ha1 : ((271611/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((544071/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e506 e506_ok ha1 ha2 hz1 hz2 hz

-- box ['544071/2048000', '13623/51200', '999/1000', '1999/2000']  interval_lower 1980341697/1099511627776
noncomputable def e507 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1391607521738,0,true,259037751872,259037751936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨807415733814,0,false,-339510158400,-339510158336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1392063325144,0,true,259397824000,259397824064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨806959930408,0,false,-340131031424,-340131031360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1391315425843,0,true,258806942144,258806942208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨807707829709,0,false,-339112463936,-339112463872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1391917049296,0,true,259282282944,259282283008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨807106206256,0,false,-339931743424,-339931743360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588614260,0,true,76983744,76983808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434641292,0,false,-76989184,-76989120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099665872505,0,true,154233856,154233920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099357383047,0,false,-154255552,-154255488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606137,0,false,-21696,-21632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622386,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1391461470476,0,true,258922350464,258922350528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨807561785076,0,false,-339311288640,-339311288576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1391990196802,0,true,259340062592,259340062656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨807033058750,0,false,-340031395968,-340031395904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1021710073723,0,false,-80691333376,-80691333312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1021991110031,0,false,-80388938176,-80388938112⟩
    { al := (544071/2048000), au := (13623/51200), zl := (999/1000), zu := (1999/2000),
      A := ⟨292095893962,292551697368⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259037751872,259037751936⟩ : DyadicInterval 40),(⟨-339510158400,-339510158336⟩ : DyadicInterval 40),(⟨722854567262,722854586592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259397824000,259397824064⟩ : DyadicInterval 40),(⟨-340131031424,-340131031360⟩ : DyadicInterval 40),(⟨722730401350,722730420680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258806942144,258806942208⟩ : DyadicInterval 40),(⟨-339112463936,-339112463872⟩ : DyadicInterval 40),(⟨722934030537,722934049867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259282282944,259282283008⟩ : DyadicInterval 40),(⟨-339931743424,-339931743360⟩ : DyadicInterval 40),(⟨722770270677,722770290007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76986484,154244729⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76983744,76983808⟩ : DyadicInterval 40),(⟨-76989184,-76989120⟩ : DyadicInterval 40),(⟨762123380881,762123400210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154233856,154233920⟩ : DyadicInterval 40),(⟨-154255552,-154255488⟩ : DyadicInterval 40),(⟨762123372761,762123392091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21696,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123413728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨291949842700,292478569026⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258922350464,258922350528⟩ : DyadicInterval 40),(⟨-339311288640,-339311288576⟩ : DyadicInterval 40),(⟨722894310213,722894329542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259340062592,259340062656⟩ : DyadicInterval 40),(⟨-340031395968,-340031395904⟩ : DyadicInterval 40),(⟨722750336000,722750355329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80691333376,-80388938112⟩ : DyadicInterval 40),(⟨802317852672,802469069568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨259037751872,259397824064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-340131031424,-339510158336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e507_ok : ecellOkT e507 = true := by decide +kernel
theorem e507_pos {a z : ℝ} (ha1 : ((544071/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13623/51200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e507 e507_ok ha1 ha2 hz1 hz2 hz

-- box ['271611/1024000', '544071/2048000', '1999/2000', '1']  interval_lower 1950108285/1099511627776
noncomputable def e508 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1391151718334,0,true,258677561792,258677561856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨807871537218,0,false,-338889635712,-338889635648⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1391607521739,0,true,259037751872,259037751936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨807415733813,0,false,-339510158400,-339510158336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1391005898288,0,true,258562305280,258562305344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨808017357264,0,false,-338691192832,-338691192768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588619008,0,true,76988480,76988544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434636544,0,false,-76993984,-76993920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622384,0,false,-5440,-5376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1391078802155,0,true,258619930176,258619930240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨807944453397,0,false,-338790401408,-338790401344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1391607530367,0,true,259037758656,259037758720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨807415725185,0,false,-339510170112,-339510170048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1021913524986,0,false,-80472411392,-80472411328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1022194194265,0,false,-80170471232,-80170471168⟩
    { al := (271611/1024000), au := (544071/2048000), zl := (1999/2000), zu := 1,
      A := ⟨291640090558,292095893963⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258677561792,258677561856⟩ : DyadicInterval 40),(⟨-338889635712,-338889635648⟩ : DyadicInterval 40),(⟨722978529847,722978549176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259037751872,259037751936⟩ : DyadicInterval 40),(⟨-339510158400,-339510158336⟩ : DyadicInterval 40),(⟨722854567262,722854586592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258562305280,258562305344⟩ : DyadicInterval 40),(⟨-338691192832,-338691192768⟩ : DyadicInterval 40),(⟨723018144922,723018164252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259037751872,259037751936⟩ : DyadicInterval 40),(⟨-339510158400,-339510158336⟩ : DyadicInterval 40),(⟨722854567262,722854586592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,76991232⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76988480,76988544⟩ : DyadicInterval 40),(⟨-76993984,-76993920⟩ : DyadicInterval 40),(⟨762123380912,762123400242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,0⟩ : DyadicInterval 40),(⟨762123383616,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨291567174379,292095902591⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258619930176,258619930240⟩ : DyadicInterval 40),(⟨-338790401408,-338790401344⟩ : DyadicInterval 40),(⟨722998341657,722998360986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259037758656,259037758720⟩ : DyadicInterval 40),(⟨-339510170112,-339510170048⟩ : DyadicInterval 40),(⟨722854564921,722854584250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80472411392,-80170471168⟩ : DyadicInterval 40),(⟨802208619200,802359608576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨258677561792,259037751936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-339510158400,-338889635648⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e508_ok : ecellOkT e508 = true := by decide +kernel
theorem e508_pos {a z : ℝ} (ha1 : ((271611/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((544071/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e508 e508_ok ha1 ha2 hz1 hz2 hz

-- box ['544071/2048000', '13623/51200', '1999/2000', '1']  interval_lower 1974506801/1099511627776
noncomputable def e509 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1391607521738,0,true,259037751872,259037751936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨807415733814,0,false,-339510158400,-339510158336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1392063325144,0,true,259397824000,259397824064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨806959930408,0,false,-340131031424,-340131031360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1391461473790,0,true,258922353088,258922353152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨807561781762,0,false,-339311293184,-339311293120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588752397,0,true,77121856,77121920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434503155,0,false,-77127360,-77127296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622366,0,false,-5440,-5376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1391534491603,0,true,258980049088,258980049152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨807488763949,0,false,-339410712896,-339410712832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1392063333773,0,true,259397830848,259397830912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨806959921779,0,false,-340131043136,-340131043072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1021671158862,0,false,-80733212288,-80733212224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1021952327044,0,false,-80430663744,-80430663680⟩
    { al := (544071/2048000), au := (13623/51200), zl := (1999/2000), zu := 1,
      A := ⟨292095893962,292551697368⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259037751872,259037751936⟩ : DyadicInterval 40),(⟨-339510158400,-339510158336⟩ : DyadicInterval 40),(⟨722854567262,722854586592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259397824000,259397824064⟩ : DyadicInterval 40),(⟨-340131031424,-340131031360⟩ : DyadicInterval 40),(⟨722730401350,722730420680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258922353088,258922353152⟩ : DyadicInterval 40),(⟨-339311293184,-339311293120⟩ : DyadicInterval 40),(⟨722894309319,722894328649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259397824000,259397824064⟩ : DyadicInterval 40),(⟨-340131031424,-340131031360⟩ : DyadicInterval 40),(⟨722730401350,722730420680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77124621⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77121856,77121920⟩ : DyadicInterval 40),(⟨-77127360,-77127296⟩ : DyadicInterval 40),(⟨762123380893,762123400223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,0⟩ : DyadicInterval 40),(⟨762123383616,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨292022863827,292551705997⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨258980049088,258980049152⟩ : DyadicInterval 40),(⟨-339410712896,-339410712832⟩ : DyadicInterval 40),(⟨722874442596,722874461926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259397830848,259397830912⟩ : DyadicInterval 40),(⟨-340131043136,-340131043072⟩ : DyadicInterval 40),(⟨722730398961,722730418290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80733212288,-80430663680⟩ : DyadicInterval 40),(⟨802338715456,802490009024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨259037751872,259397824064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-340131031424,-339510158336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e509_ok : ecellOkT e509 = true := by decide +kernel
theorem e509_pos {a z : ℝ} (ha1 : ((544071/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13623/51200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e509 e509_ok ha1 ha2 hz1 hz2 hz

-- box ['13623/51200', '545769/2048000', '999/1000', '1999/2000']  interval_lower 501232355/274877906944
noncomputable def e510 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1392063325143,0,true,259397824000,259397824064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨806959930409,0,false,-340131031424,-340131031360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1392519128548,0,true,259757778240,259757778304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨806504127004,0,false,-340752255232,-340752255168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1391770773445,0,true,259166729792,259166729856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨807252482107,0,false,-339732491520,-339732491456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1392372624798,0,true,259642095040,259642095104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨806650630754,0,false,-340552544000,-340552543936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588747627,0,true,77117120,77117184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434507925,0,false,-77122560,-77122496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099666139396,0,true,154500736,154500800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099357116156,0,false,-154522496,-154522432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511606062,0,false,-21760,-21696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622367,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1391917045994,0,true,259282280320,259282280384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨807106209558,0,false,-339931738944,-339931738880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1392445886258,0,true,259699945728,259699945792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨806577369294,0,false,-340652408128,-340652408064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1021467451048,0,false,-80952462336,-80952462272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1021748986215,0,false,-80649458560,-80649458496⟩
    { al := (13623/51200), au := (545769/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨292551697367,293007500772⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259397824000,259397824064⟩ : DyadicInterval 40),(⟨-340131031424,-340131031360⟩ : DyadicInterval 40),(⟨722730401351,722730420680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259757778240,259757778304⟩ : DyadicInterval 40),(⟨-340752255232,-340752255168⟩ : DyadicInterval 40),(⟨722606032092,722606051421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259166729792,259166729856⟩ : DyadicInterval 40),(⟨-339732491520,-339732491456⟩ : DyadicInterval 40),(⟨722810119026,722810138356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259642095040,259642095104⟩ : DyadicInterval 40),(⟨-340552544000,-340552543936⟩ : DyadicInterval 40),(⟨722646028895,722646048225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77119851,154511620⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77117120,77117184⟩ : DyadicInterval 40),(⟨-77122560,-77122496⟩ : DyadicInterval 40),(⟨762123380862,762123400191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154500736,154500800⟩ : DyadicInterval 40),(⟨-154522496,-154522432⟩ : DyadicInterval 40),(⟨762123372718,762123392048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21760,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123413760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨292405418218,292934258482⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259282280320,259282280384⟩ : DyadicInterval 40),(⟨-339931738944,-339931738880⟩ : DyadicInterval 40),(⟨722770271593,722770290923⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259699945728,259699945792⟩ : DyadicInterval 40),(⟨-340652408128,-340652408064⟩ : DyadicInterval 40),(⟨722626030497,722626049827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80952462336,-80649458496⟩ : DyadicInterval 40),(⟨802448112864,802599634048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨259397824000,259757778304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-340752255232,-340131031360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e510_ok : ecellOkT e510 = true := by decide +kernel
theorem e510_pos {a z : ℝ} (ha1 : ((13623/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((545769/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e510 e510_ok ha1 ha2 hz1 hz2 hz

-- box ['545769/2048000', '273309/1024000', '999/1000', '1999/2000']  interval_lower 507417787/274877906944
noncomputable def e511 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1392519128547,0,true,259757778240,259757778304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨806504127005,0,false,-340752255232,-340752255168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1392974931952,0,true,260117614720,260117614784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨806048323600,0,false,-341373830272,-341373830208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1392226121046,0,true,259526399680,259526399744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨806797134506,0,false,-340352868992,-340352868928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1392828200301,0,true,260001789440,260001789504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨806195055251,0,false,-341173695232,-341173695168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588881062,0,true,77250560,77250624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434374490,0,false,-77256064,-77256000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099666406423,0,true,154767744,154767808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099356849129,0,false,-154789568,-154789504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605987,0,false,-21824,-21760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622349,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1392372621498,0,true,259642092480,259642092544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨806650634054,0,false,-340552539456,-340552539392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1392901575721,0,true,260059711168,260059711232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨806121679831,0,false,-341273771264,-341273771200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1021224450650,0,false,-81214060096,-81214060032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1021506484877,0,false,-80910446976,-80910446912⟩
    { al := (545769/2048000), au := (273309/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨293007500771,293463304176⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259757778240,259757778304⟩ : DyadicInterval 40),(⟨-340752255232,-340752255168⟩ : DyadicInterval 40),(⟨722606032092,722606051421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260117614720,260117614784⟩ : DyadicInterval 40),(⟨-341373830272,-341373830208⟩ : DyadicInterval 40),(⟨722481459423,722481478753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259526399680,259526399744⟩ : DyadicInterval 40),(⟨-340352868992,-340352868928⟩ : DyadicInterval 40),(⟨722686004664,722686023993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260001789440,260001789504⟩ : DyadicInterval 40),(⟨-341173695232,-341173695168⟩ : DyadicInterval 40),(⟨722521583905,722521603235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77253286,154778647⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77250560,77250624⟩ : DyadicInterval 40),(⟨-77256064,-77256000⟩ : DyadicInterval 40),(⟨762123380875,762123400205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154767744,154767808⟩ : DyadicInterval 40),(⟨-154789568,-154789504⟩ : DyadicInterval 40),(⟨762123372675,762123392005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21824,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123413792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨292860993722,293389947945⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259642092480,259642092544⟩ : DyadicInterval 40),(⟨-340552539456,-340552539392⟩ : DyadicInterval 40),(⟨722646029750,722646049080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260059711168,260059711232⟩ : DyadicInterval 40),(⟨-341273771264,-341273771200⟩ : DyadicInterval 40),(⟨722501521675,722501541005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-81214060096,-80910446912⟩ : DyadicInterval 40),(⟨802578607072,802730432928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨259757778240,260117614784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-341373830272,-340752255168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e511_ok : ecellOkT e511 = true := by decide +kernel
theorem e511_pos {a z : ℝ} (ha1 : ((545769/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273309/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e511 e511_ok ha1 ha2 hz1 hz2 hz

-- box ['13623/51200', '545769/2048000', '1999/2000', '1']  interval_lower 1999058497/1099511627776
noncomputable def e512 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1392063325143,0,true,259397824000,259397824064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨806959930409,0,false,-340131031424,-340131031360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1392519128548,0,true,259757778240,259757778304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨806504127004,0,false,-340752255232,-340752255168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1391917049294,0,true,259282282944,259282283008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨807106206258,0,false,-339931743424,-339931743360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588885854,0,true,77255360,77255424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434369698,0,false,-77260800,-77260736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622347,0,false,-5440,-5376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1391990181049,0,true,259340050112,259340050176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨807033074503,0,false,-340031374464,-340031374400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1392519137177,0,true,259757785088,259757785152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨806504118375,0,false,-340752267008,-340752266944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1021428414832,0,false,-80994481920,-80994481856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1021710082105,0,false,-80691324352,-80691324288⟩
    { al := (13623/51200), au := (545769/2048000), zl := (1999/2000), zu := 1,
      A := ⟨292551697367,293007500772⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259397824000,259397824064⟩ : DyadicInterval 40),(⟨-340131031424,-340131031360⟩ : DyadicInterval 40),(⟨722730401351,722730420680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259757778240,259757778304⟩ : DyadicInterval 40),(⟨-340752255232,-340752255168⟩ : DyadicInterval 40),(⟨722606032092,722606051421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259282282944,259282283008⟩ : DyadicInterval 40),(⟨-339931743424,-339931743360⟩ : DyadicInterval 40),(⟨722770270677,722770290007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259757778240,259757778304⟩ : DyadicInterval 40),(⟨-340752255232,-340752255168⟩ : DyadicInterval 40),(⟨722606032092,722606051421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77258078⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77255360,77255424⟩ : DyadicInterval 40),(⟨-77260800,-77260736⟩ : DyadicInterval 40),(⟨762123380843,762123400172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,0⟩ : DyadicInterval 40),(⟨762123383616,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨292478553273,293007509401⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259340050112,259340050176⟩ : DyadicInterval 40),(⟨-340031374464,-340031374400⟩ : DyadicInterval 40),(⟨722750340302,722750359631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259757785088,259757785152⟩ : DyadicInterval 40),(⟨-340752267008,-340752266944⟩ : DyadicInterval 40),(⟨722606029717,722606049047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-80994481920,-80691324288⟩ : DyadicInterval 40),(⟨802469045760,802620643840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨259397824000,259757778304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-340752255232,-340131031360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e512_ok : ecellOkT e512 = true := by decide +kernel
theorem e512_pos {a z : ℝ} (ha1 : ((13623/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((545769/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e512 e512_ok ha1 ha2 hz1 hz2 hz

-- box ['545769/2048000', '273309/1024000', '1999/2000', '1']  interval_lower 1011881979/549755813888
noncomputable def e513 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1392519128547,0,true,259757778240,259757778304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨806504127005,0,false,-340752255232,-340752255168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1392974931952,0,true,260117614720,260117614784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨806048323600,0,false,-341373830272,-341373830208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1392372624796,0,true,259642095040,259642095104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨806650630756,0,false,-340552544000,-340552543936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589019378,0,true,77388864,77388928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434236174,0,false,-77394368,-77394304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622328,0,false,-5504,-5440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1392445870495,0,true,259699933312,259699933376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨806577385057,0,false,-340652386624,-340652386560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1392974940585,0,true,260117621504,260117621568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨806048314967,0,false,-341373842048,-341373841984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1021185292893,0,false,-81256220480,-81256220416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1021467459448,0,false,-80952453312,-80952453248⟩
    { al := (545769/2048000), au := (273309/1024000), zl := (1999/2000), zu := 1,
      A := ⟨293007500771,293463304176⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259757778240,259757778304⟩ : DyadicInterval 40),(⟨-340752255232,-340752255168⟩ : DyadicInterval 40),(⟨722606032092,722606051421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260117614720,260117614784⟩ : DyadicInterval 40),(⟨-341373830272,-341373830208⟩ : DyadicInterval 40),(⟨722481459423,722481478753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259642095040,259642095104⟩ : DyadicInterval 40),(⟨-340552544000,-340552543936⟩ : DyadicInterval 40),(⟨722646028896,722646048225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260117614720,260117614784⟩ : DyadicInterval 40),(⟨-341373830272,-341373830208⟩ : DyadicInterval 40),(⟨722481459423,722481478753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77391602⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77388864,77388928⟩ : DyadicInterval 40),(⟨-77394368,-77394304⟩ : DyadicInterval 40),(⟨762123380856,762123400185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,0⟩ : DyadicInterval 40),(⟨762123383616,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨292934242719,293463312809⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259699933312,259699933376⟩ : DyadicInterval 40),(⟨-340652386624,-340652386560⟩ : DyadicInterval 40),(⟨722626034775,722626054105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260117621504,260117621568⟩ : DyadicInterval 40),(⟨-341373842048,-341373841984⟩ : DyadicInterval 40),(⟨722481457081,722481476411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-81256220480,-80952453248⟩ : DyadicInterval 40),(⟨802599610240,802751513120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨259757778240,260117614784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-341373830272,-340752255168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e513_ok : ecellOkT e513 = true := by decide +kernel
theorem e513_pos {a z : ℝ} (ha1 : ((545769/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273309/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e513 e513_ok ha1 ha2 hz1 hz2 hz

-- box ['273309/1024000', '547467/2048000', '999/1000', '1999/2000']  interval_lower 1027283889/549755813888
noncomputable def e514 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1392974931951,0,true,260117614720,260117614784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨806048323601,0,false,-341373830272,-341373830208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1393430735356,0,true,260477333440,260477333504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨805592520196,0,false,-341995756864,-341995756800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1392681468646,0,true,259885952000,259885952064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨806341786906,0,false,-340973596672,-340973596608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1393283775803,0,true,260361366208,260361366272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨805739479749,0,false,-341795197632,-341795197568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589014563,0,true,77384000,77384064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434240989,0,false,-77389568,-77389504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099666673585,0,true,155034816,155034880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099356581967,0,false,-155056768,-155056704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605912,0,false,-21888,-21824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622330,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1392828197011,0,true,260001786880,260001786944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨806195058541,0,false,-341173690752,-341173690688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1393357265179,0,true,260419358912,260419358976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨805665990373,0,false,-341895485760,-341895485696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1020981072537,0,false,-81476126784,-81476126720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1021263606005,0,false,-81171903872,-81171903808⟩
    { al := (273309/1024000), au := (547467/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨293463304175,293919107580⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260117614720,260117614784⟩ : DyadicInterval 40),(⟨-341373830272,-341373830208⟩ : DyadicInterval 40),(⟨722481459423,722481478753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260477333440,260477333504⟩ : DyadicInterval 40),(⟨-341995756864,-341995756800⟩ : DyadicInterval 40),(⟨722356683318,722356702647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨259885952000,259885952064⟩ : DyadicInterval 40),(⟨-340973596672,-340973596608⟩ : DyadicInterval 40),(⟨722561687301,722561706630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260361366208,260361366272⟩ : DyadicInterval 40),(⟨-341795197632,-341795197568⟩ : DyadicInterval 40),(⟨722396935710,722396955040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77386787,155045809⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77384000,77384064⟩ : DyadicInterval 40),(⟨-77389568,-77389504⟩ : DyadicInterval 40),(⟨762123380889,762123400218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155034816,155034880⟩ : DyadicInterval 40),(⟨-155056768,-155056704⟩ : DyadicInterval 40),(⟨762123372664,762123391993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21888,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123413824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨293316569235,293845637403⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260001786880,260001786944⟩ : DyadicInterval 40),(⟨-341173690752,-341173690688⟩ : DyadicInterval 40),(⟨722521584784,722521604113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260419358912,260419358976⟩ : DyadicInterval 40),(⟨-341895485760,-341895485696⟩ : DyadicInterval 40),(⟨722376809533,722376828863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-81476126784,-81171903808⟩ : DyadicInterval 40),(⟨802709335520,802861466272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨260117614720,260477333504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-341995756864,-341373830208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e514_ok : ecellOkT e514 = true := by decide +kernel
theorem e514_pos {a z : ℝ} (ha1 : ((273309/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((547467/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e514 e514_ok ha1 ha2 hz1 hz2 hz

-- box ['547467/2048000', '137079/512000', '999/1000', '1999/2000']  interval_lower 1039809685/549755813888
noncomputable def e515 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1393430735355,0,true,260477333440,260477333504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨805592520197,0,false,-341995756864,-341995756800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1393886538761,0,true,260836934528,260836934592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨805136716791,0,false,-342618035456,-342618035392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1393136816247,0,true,260245386816,260245386880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨805886439305,0,false,-341594675008,-341594674944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1393739351306,0,true,260720825472,260720825536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨805283904246,0,false,-342417051520,-342417051456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589148134,0,true,77517568,77517632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434107418,0,false,-77523136,-77523072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099666940883,0,true,155302080,155302144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099356314669,0,false,-155324096,-155324032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605837,0,false,-21952,-21888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622311,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1393283772527,0,true,260361363648,260361363712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨805739483025,0,false,-341795193152,-341795193088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1393812954645,0,true,260778889088,260778889152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨805210300907,0,false,-342517552000,-342517551936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1020737316701,0,false,-81738662912,-81738662848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1021020349602,0,false,-81433829504,-81433829440⟩
    { al := (547467/2048000), au := (137079/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨293919107579,294374910985⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260477333440,260477333504⟩ : DyadicInterval 40),(⟨-341995756864,-341995756800⟩ : DyadicInterval 40),(⟨722356683318,722356702647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260836934528,260836934592⟩ : DyadicInterval 40),(⟨-342618035456,-342618035392⟩ : DyadicInterval 40),(⟨722231703712,722231723042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260245386816,260245386880⟩ : DyadicInterval 40),(⟨-341594675008,-341594674944⟩ : DyadicInterval 40),(⟨722437166917,722437186246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260720825472,260720825536⟩ : DyadicInterval 40),(⟨-342417051520,-342417051456⟩ : DyadicInterval 40),(⟨722272084200,722272103530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77520358,155313107⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77517568,77517632⟩ : DyadicInterval 40),(⟨-77523136,-77523072⟩ : DyadicInterval 40),(⟨762123380870,762123400199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155302080,155302144⟩ : DyadicInterval 40),(⟨-155324096,-155324032⟩ : DyadicInterval 40),(⟨762123372620,762123391950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-21952,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123413856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨293772144751,294301326869⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260361363648,260361363712⟩ : DyadicInterval 40),(⟨-341795193152,-341795193088⟩ : DyadicInterval 40),(⟨722396936588,722396955917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260778889088,260778889152⟩ : DyadicInterval 40),(⟨-342517552000,-342517551936⟩ : DyadicInterval 40),(⟨722251893982,722251913311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-81738662912,-81433829440⟩ : DyadicInterval 40),(⟨802840298336,802992734336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨260477333440,260836934592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-342618035456,-341995756800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e515_ok : ecellOkT e515 = true := by decide +kernel
theorem e515_pos {a z : ℝ} (ha1 : ((547467/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137079/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e515 e515_ok ha1 ha2 hz1 hz2 hz

-- box ['273309/1024000', '547467/2048000', '1999/2000', '1']  interval_lower 1024311983/549755813888
noncomputable def e516 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1392974931951,0,true,260117614720,260117614784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨806048323601,0,false,-341373830272,-341373830208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1393430735356,0,true,260477333440,260477333504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨805592520196,0,false,-341995756864,-341995756800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1392828200298,0,true,260001789440,260001789504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨806195055254,0,false,-341173695232,-341173695168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589152970,0,true,77522432,77522496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434102582,0,false,-77527936,-77527872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622309,0,false,-5504,-5440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1392901559948,0,true,260059698752,260059698816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨806121695604,0,false,-341273749760,-341273749696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1393430743989,0,true,260477340224,260477340288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨805592511563,0,false,-341995768640,-341995768576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1020941793048,0,false,-81518428352,-81518428288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1021224459069,0,false,-81214051008,-81214050944⟩
    { al := (273309/1024000), au := (547467/2048000), zl := (1999/2000), zu := 1,
      A := ⟨293463304175,293919107580⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260117614720,260117614784⟩ : DyadicInterval 40),(⟨-341373830272,-341373830208⟩ : DyadicInterval 40),(⟨722481459423,722481478753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260477333440,260477333504⟩ : DyadicInterval 40),(⟨-341995756864,-341995756800⟩ : DyadicInterval 40),(⟨722356683318,722356702647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260001789440,260001789504⟩ : DyadicInterval 40),(⟨-341173695232,-341173695168⟩ : DyadicInterval 40),(⟨722521583906,722521603236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260477333440,260477333504⟩ : DyadicInterval 40),(⟨-341995756864,-341995756800⟩ : DyadicInterval 40),(⟨722356683318,722356702647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77525194⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77522432,77522496⟩ : DyadicInterval 40),(⟨-77527936,-77527872⟩ : DyadicInterval 40),(⟨762123380837,762123400166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,0⟩ : DyadicInterval 40),(⟨762123383616,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨293389932172,293919116213⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260059698752,260059698816⟩ : DyadicInterval 40),(⟨-341273749760,-341273749696⟩ : DyadicInterval 40),(⟨722501525970,722501545300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260477340224,260477340288⟩ : DyadicInterval 40),(⟨-341995768640,-341995768576⟩ : DyadicInterval 40),(⟨722356680967,722356700297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-81518428352,-81214050944⟩ : DyadicInterval 40),(⟨802730409088,802882617056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨260117614720,260477333504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-341995756864,-341373830208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e516_ok : ecellOkT e516 = true := by decide +kernel
theorem e516_pos {a z : ℝ} (ha1 : ((273309/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((547467/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e516 e516_ok ha1 ha2 hz1 hz2 hz

-- box ['547467/2048000', '137079/512000', '1999/2000', '1']  interval_lower 1036819505/549755813888
noncomputable def e517 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1393430735355,0,true,260477333440,260477333504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨805592520197,0,false,-341995756864,-341995756800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1393886538761,0,true,260836934528,260836934592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨805136716791,0,false,-342618035456,-342618035392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1393283775801,0,true,260361366208,260361366272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨805739479751,0,false,-341795197632,-341795197568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589286630,0,true,77656064,77656128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433968922,0,false,-77661632,-77661568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622290,0,false,-5504,-5440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1393357249396,0,true,260419346496,260419346560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨805666006156,0,false,-341895464256,-341895464192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1393886547397,0,true,260836941312,260836941376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨805136708155,0,false,-342618047232,-342618047168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1020697915294,0,false,-81781105856,-81781105792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1020981080974,0,false,-81476117696,-81476117632⟩
    { al := (547467/2048000), au := (137079/512000), zl := (1999/2000), zu := 1,
      A := ⟨293919107579,294374910985⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260477333440,260477333504⟩ : DyadicInterval 40),(⟨-341995756864,-341995756800⟩ : DyadicInterval 40),(⟨722356683318,722356702647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260836934528,260836934592⟩ : DyadicInterval 40),(⟨-342618035456,-342618035392⟩ : DyadicInterval 40),(⟨722231703712,722231723042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260361366208,260361366272⟩ : DyadicInterval 40),(⟨-341795197632,-341795197568⟩ : DyadicInterval 40),(⟨722396935711,722396955040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260836934528,260836934592⟩ : DyadicInterval 40),(⟨-342618035456,-342618035392⟩ : DyadicInterval 40),(⟨722231703712,722231723042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77658854⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77656064,77656128⟩ : DyadicInterval 40),(⟨-77661632,-77661568⟩ : DyadicInterval 40),(⟨762123380850,762123400180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,0⟩ : DyadicInterval 40),(⟨762123383616,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨293845621620,294374919621⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260419346496,260419346560⟩ : DyadicInterval 40),(⟨-341895464256,-341895464192⟩ : DyadicInterval 40),(⟨722376813845,722376833174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260836941312,260836941376⟩ : DyadicInterval 40),(⟨-342618047232,-342618047168⟩ : DyadicInterval 40),(⟨722231701354,722231720683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-81781105856,-81476117632⟩ : DyadicInterval 40),(⟨802861442432,803013955808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨260477333440,260836934592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-342618035456,-341995756800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e517_ok : ecellOkT e517 = true := by decide +kernel
theorem e517_pos {a z : ℝ} (ha1 : ((547467/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137079/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e517 e517_ok ha1 ha2 hz1 hz2 hz

-- box ['137079/512000', '109833/409600', '999/1000', '1999/2000']  interval_lower 2104827115/1099511627776
noncomputable def e518 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1393886538760,0,true,260836934528,260836934592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨805136716792,0,false,-342618035456,-342618035392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1394342342165,0,true,261196417984,261196418048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨804680913387,0,false,-343240666432,-343240666368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1393592163848,0,true,260604704128,260604704192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨805431091704,0,false,-342216104320,-342216104256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1394194926809,0,true,261080167168,261080167232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨804828328743,0,false,-343039257280,-343039257216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589281772,0,true,77651200,77651264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433973780,0,false,-77656768,-77656704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099667208318,0,true,155569472,155569536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099356047234,0,false,-155591552,-155591488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605761,0,false,-22016,-21952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622292,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1393739348041,0,true,260720822848,260720822912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨805283907511,0,false,-342417047040,-342417046976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1394268644094,0,true,261138301696,261138301760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨804754611458,0,false,-343139970368,-343139970304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1020493183155,0,false,-82001668608,-82001668544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1020776715671,0,false,-81696224192,-81696224128⟩
    { al := (137079/512000), au := (109833/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨294374910984,294830714389⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260836934528,260836934592⟩ : DyadicInterval 40),(⟨-342618035456,-342618035392⟩ : DyadicInterval 40),(⟨722231703712,722231723042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261196417984,261196418048⟩ : DyadicInterval 40),(⟨-343240666432,-343240666368⟩ : DyadicInterval 40),(⟨722106520601,722106539931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260604704128,260604704192⟩ : DyadicInterval 40),(⟨-342216104320,-342216104256⟩ : DyadicInterval 40),(⟨722312443484,722312462813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261080167168,261080167232⟩ : DyadicInterval 40),(⟨-343039257280,-343039257216⟩ : DyadicInterval 40),(⟨722147029411,722147048741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77653996,155580542⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77651200,77651264⟩ : DyadicInterval 40),(⟨-77656768,-77656704⟩ : DyadicInterval 40),(⟨762123380851,762123400180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155569472,155569536⟩ : DyadicInterval 40),(⟨-155591552,-155591488⟩ : DyadicInterval 40),(⟨762123372576,762123391906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22016,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123413888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨294227720265,294757016318⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260720822848,260720822912⟩ : DyadicInterval 40),(⟨-342417047040,-342417046976⟩ : DyadicInterval 40),(⟨722272085118,722272104448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261138301696,261138301760⟩ : DyadicInterval 40),(⟨-343139970368,-343139970304⟩ : DyadicInterval 40),(⟨722126775023,722126794352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82001668608,-81696224128⟩ : DyadicInterval 40),(⟨802971495680,803124237184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨260836934528,261196418048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-343240666432,-342618035392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e518_ok : ecellOkT e518 = true := by decide +kernel
theorem e518_pos {a z : ℝ} (ha1 : ((137079/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((109833/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e518 e518_ok ha1 ha2 hz1 hz2 hz

-- box ['109833/409600', '275007/1024000', '999/1000', '1999/2000']  interval_lower 2130191083/1099511627776
noncomputable def e519 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1394342342164,0,true,261196417984,261196418048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨804680913388,0,false,-343240666432,-343240666368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1394798145569,0,true,261555784000,261555784064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨804225109983,0,false,-343863650176,-343863650112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1394047511449,0,true,260963904064,260963904128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨804975744103,0,false,-342837885120,-342837885056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1394650502311,0,true,261439391488,261439391552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨804372753241,0,false,-343661815424,-343661815360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589415479,0,true,77784896,77784960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433840073,0,false,-77790464,-77790400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099667475889,0,true,155837056,155837120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099355779663,0,false,-155859200,-155859136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605685,0,false,-22144,-22080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622273,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1394194923545,0,true,261080164608,261080164672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨804828332007,0,false,-343039252864,-343039252800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1394724333549,0,true,261497596864,261497596928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨804298922003,0,false,-343762741312,-343762741248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1020248671888,0,false,-82265144384,-82265144320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1020532704215,0,false,-81959088192,-81959088128⟩
    { al := (109833/409600), au := (275007/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨294830714388,295286517793⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261196417984,261196418048⟩ : DyadicInterval 40),(⟨-343240666432,-343240666368⟩ : DyadicInterval 40),(⟨722106520602,722106539931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261555784000,261555784064⟩ : DyadicInterval 40),(⟨-343863650176,-343863650112⟩ : DyadicInterval 40),(⟨721981133859,721981153188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260963904064,260963904128⟩ : DyadicInterval 40),(⟨-342837885120,-342837885056⟩ : DyadicInterval 40),(⟨722187516963,722187536293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261439391488,261439391552⟩ : DyadicInterval 40),(⟨-343661815424,-343661815360⟩ : DyadicInterval 40),(⟨722021771263,722021790593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77787703,155848113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77784896,77784960⟩ : DyadicInterval 40),(⟨-77790464,-77790400⟩ : DyadicInterval 40),(⟨762123380832,762123400161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155837056,155837120⟩ : DyadicInterval 40),(⟨-155859200,-155859136⟩ : DyadicInterval 40),(⟨762123372533,762123391863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22144,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123413952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨294683295769,295212705773⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261080164608,261080164672⟩ : DyadicInterval 40),(⟨-343039252864,-343039252800⟩ : DyadicInterval 40),(⟨722147030315,722147049644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261497596864,261497596928⟩ : DyadicInterval 40),(⟨-343762741312,-343762741248⟩ : DyadicInterval 40),(⟨722001452587,722001471916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82265144384,-81959088128⟩ : DyadicInterval 40),(⟨803102927680,803255975072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨261196417984,261555784064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-343863650176,-343240666368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e519_ok : ecellOkT e519 = true := by decide +kernel
theorem e519_pos {a z : ℝ} (ha1 : ((109833/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((275007/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e519 e519_ok ha1 ha2 hz1 hz2 hz

-- box ['137079/512000', '109833/409600', '1999/2000', '1']  interval_lower 1049404881/549755813888
noncomputable def e520 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1393886538760,0,true,260836934528,260836934592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨805136716792,0,false,-342618035456,-342618035392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1394342342165,0,true,261196417984,261196418048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨804680913387,0,false,-343240666432,-343240666368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1393739351304,0,true,260720825408,260720825472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨805283904248,0,false,-342417051520,-342417051456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589420358,0,true,77789824,77789888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433835194,0,false,-77795392,-77795328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622272,0,false,-5568,-5504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1393812938845,0,true,260778876608,260778876672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨805210316707,0,false,-342517530432,-342517530368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1394342350789,0,true,261196424832,261196424896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨804680904763,0,false,-343240678208,-343240678144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1020453659641,0,false,-82044253312,-82044253248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1020737325160,0,false,-81738653760,-81738653696⟩
    { al := (137079/512000), au := (109833/409600), zl := (1999/2000), zu := 1,
      A := ⟨294374910984,294830714389⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260836934528,260836934592⟩ : DyadicInterval 40),(⟨-342618035456,-342618035392⟩ : DyadicInterval 40),(⟨722231703712,722231723042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261196417984,261196418048⟩ : DyadicInterval 40),(⟨-343240666432,-343240666368⟩ : DyadicInterval 40),(⟨722106520601,722106539931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260720825408,260720825472⟩ : DyadicInterval 40),(⟨-342417051520,-342417051456⟩ : DyadicInterval 40),(⟨722272084241,722272103571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261196417984,261196418048⟩ : DyadicInterval 40),(⟨-343240666432,-343240666368⟩ : DyadicInterval 40),(⟨722106520601,722106539931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77792582⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77789824,77789888⟩ : DyadicInterval 40),(⟨-77795392,-77795328⟩ : DyadicInterval 40),(⟨762123380831,762123400161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,0⟩ : DyadicInterval 40),(⟨762123383616,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨294301311069,294830723013⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨260778876608,260778876672⟩ : DyadicInterval 40),(⟨-342517530432,-342517530368⟩ : DyadicInterval 40),(⟨722251898329,722251917659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261196424832,261196424896⟩ : DyadicInterval 40),(⟨-343240678208,-343240678144⟩ : DyadicInterval 40),(⟨722106518198,722106537527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82044253312,-81738653696⟩ : DyadicInterval 40),(⟨802992710464,803145529536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨260836934528,261196418048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-343240666432,-342618035392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e520_ok : ecellOkT e520 = true := by decide +kernel
theorem e520_pos {a z : ℝ} (ha1 : ((137079/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((109833/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e520 e520_ok ha1 ha2 hz1 hz2 hz

-- box ['109833/409600', '275007/1024000', '1999/2000', '1']  interval_lower 2124136975/1099511627776
noncomputable def e521 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1394342342164,0,true,261196417984,261196418048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨804680913388,0,false,-343240666432,-343240666368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1394798145569,0,true,261555784000,261555784064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨804225109983,0,false,-343863650176,-343863650112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1394194926806,0,true,261080167168,261080167232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨804828328746,0,false,-343039257280,-343039257216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589554155,0,true,77923584,77923648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433701397,0,false,-77929152,-77929088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622253,0,false,-5568,-5504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1394268628293,0,true,261138289216,261138289280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨804754627259,0,false,-343139948800,-343139948736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1394798154195,0,true,261555790848,261555790912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨804225101357,0,false,-343863661952,-343863661888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1020209026073,0,false,-82307871104,-82307871040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1020493191628,0,false,-82001659520,-82001659456⟩
    { al := (109833/409600), au := (275007/1024000), zl := (1999/2000), zu := 1,
      A := ⟨294830714388,295286517793⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261196417984,261196418048⟩ : DyadicInterval 40),(⟨-343240666432,-343240666368⟩ : DyadicInterval 40),(⟨722106520602,722106539931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261555784000,261555784064⟩ : DyadicInterval 40),(⟨-343863650176,-343863650112⟩ : DyadicInterval 40),(⟨721981133859,721981153188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261080167168,261080167232⟩ : DyadicInterval 40),(⟨-343039257280,-343039257216⟩ : DyadicInterval 40),(⟨722147029412,722147048741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261555784000,261555784064⟩ : DyadicInterval 40),(⟨-343863650176,-343863650112⟩ : DyadicInterval 40),(⟨721981133859,721981153188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,77926379⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77923584,77923648⟩ : DyadicInterval 40),(⟨-77929152,-77929088⟩ : DyadicInterval 40),(⟨762123380812,762123400142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,0⟩ : DyadicInterval 40),(⟨762123383616,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨294757000517,295286526419⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261138289216,261138289280⟩ : DyadicInterval 40),(⟨-343139948800,-343139948736⟩ : DyadicInterval 40),(⟨722126779385,722126798714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261555790848,261555790912⟩ : DyadicInterval 40),(⟨-343863661952,-343863661888⟩ : DyadicInterval 40),(⟨721981131447,721981150776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82307871104,-82001659456⟩ : DyadicInterval 40),(⟨803124213344,803277338432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨261196417984,261555784064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-343863650176,-343240666368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e521_ok : ecellOkT e521 = true := by decide +kernel
theorem e521_pos {a z : ℝ} (ha1 : ((109833/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((275007/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e521 e521_ok ha1 ha2 hz1 hz2 hz

-- box ['275007/1024000', '550863/2048000', '999/1000', '1999/2000']  interval_lower 2155712675/1099511627776
noncomputable def e522 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1394798145568,0,true,261555784000,261555784064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨804225109984,0,false,-343863650176,-343863650112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1395253948974,0,true,261915032640,261915032704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨803769306578,0,false,-344486987072,-344486987008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1394502859050,0,true,261322986688,261322986752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨804520396502,0,false,-343460017664,-343460017600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1395106077814,0,true,261798498496,261798498560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨803917177738,0,false,-344284726208,-344284726144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589549254,0,true,77918656,77918720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433706298,0,false,-77924288,-77924224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099667743598,0,true,156104704,156104768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099355511954,0,false,-156126912,-156126848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605609,0,false,-22208,-22144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622254,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1394650499061,0,true,261439388928,261439388992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨804372756491,0,false,-343661810944,-343661810880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1395180023016,0,true,261856774720,261856774784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨803843232536,0,false,-344385865152,-344385865088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1020003782897,0,false,-82529090432,-82529090368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1020288315223,0,false,-82222421952,-82222421888⟩
    { al := (275007/1024000), au := (550863/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨295286517792,295742321198⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261555784000,261555784064⟩ : DyadicInterval 40),(⟨-343863650176,-343863650112⟩ : DyadicInterval 40),(⟨721981133859,721981153189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261915032640,261915032704⟩ : DyadicInterval 40),(⟨-344486987072,-344486987008⟩ : DyadicInterval 40),(⟨721855543437,721855562766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261322986688,261322986752⟩ : DyadicInterval 40),(⟨-343460017664,-343460017600⟩ : DyadicInterval 40),(⟨722062387263,722062406593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261798498496,261798498560⟩ : DyadicInterval 40),(⟨-344284726208,-344284726144⟩ : DyadicInterval 40),(⟨721896309663,721896328992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77921478,156115822⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77918656,77918720⟩ : DyadicInterval 40),(⟨-77924288,-77924224⟩ : DyadicInterval 40),(⟨762123380845,762123400174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156104704,156104768⟩ : DyadicInterval 40),(⟨-156126912,-156126848⟩ : DyadicInterval 40),(⟨762123372489,762123391819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22208,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123413984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨295138871285,295668395240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261439388928,261439388992⟩ : DyadicInterval 40),(⟨-343661810944,-343661810880⟩ : DyadicInterval 40),(⟨722021772142,722021791472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261856774720,261856774784⟩ : DyadicInterval 40),(⟨-344385865152,-344385865088⟩ : DyadicInterval 40),(⟨721875926561,721875945891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82529090432,-82222421888⟩ : DyadicInterval 40),(⟨803234594560,803387948096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨261555784000,261915032704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-344486987072,-343863650112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e522_ok : ecellOkT e522 = true := by decide +kernel
theorem e522_pos {a z : ℝ} (ha1 : ((275007/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((550863/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e522 e522_ok ha1 ha2 hz1 hz2 hz

-- box ['550863/2048000', '17241/64000', '999/1000', '1999/2000']  interval_lower 545348079/274877906944
noncomputable def e523 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1395253948973,0,true,261915032640,261915032704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨803769306579,0,false,-344486987072,-344486987008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1395709752378,0,true,262274163904,262274163968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨803313503174,0,false,-345110677632,-345110677568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1394958206651,0,true,261681952064,261681952128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨804065048901,0,false,-344082502464,-344082502400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1395561653316,0,true,262157488256,262157488320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨803461602236,0,false,-344907990080,-344907990016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589683097,0,true,78052544,78052608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433572455,0,false,-78058112,-78058048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099668011444,0,true,156372544,156372608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099355244108,0,false,-156394816,-156394752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605533,0,false,-22272,-22208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622235,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1395106074580,0,true,261798495936,261798496000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨803917180972,0,false,-344284721792,-344284721728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1395635712475,0,true,262215835200,262215835264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨803387543077,0,false,-345009342336,-345009342272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1019758516191,0,false,-82793507136,-82793507072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1020043548700,0,false,-82486225792,-82486225728⟩
    { al := (550863/2048000), au := (17241/64000), zl := (999/1000), zu := (1999/2000),
      A := ⟨295742321197,296198124602⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261915032640,261915032704⟩ : DyadicInterval 40),(⟨-344486987072,-344486987008⟩ : DyadicInterval 40),(⟨721855543437,721855562766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262274163904,262274163968⟩ : DyadicInterval 40),(⟨-345110677632,-345110677568⟩ : DyadicInterval 40),(⟨721729749377,721729768706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261681952064,261681952128⟩ : DyadicInterval 40),(⟨-344082502464,-344082502400⟩ : DyadicInterval 40),(⟨721937054384,721937073713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262157488256,262157488320⟩ : DyadicInterval 40),(⟨-344907990080,-344907990016⟩ : DyadicInterval 40),(⟨721770644588,721770663917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78055321,156383668⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78052544,78052608⟩ : DyadicInterval 40),(⟨-78058112,-78058048⟩ : DyadicInterval 40),(⟨762123380794,762123400123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156372544,156372608⟩ : DyadicInterval 40),(⟨-156394816,-156394752⟩ : DyadicInterval 40),(⟨762123372445,762123391774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22272,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123414016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨295594446804,296124084699⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261798495936,261798496000⟩ : DyadicInterval 40),(⟨-344284721792,-344284721728⟩ : DyadicInterval 40),(⟨721896310564,721896329894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262215835200,262215835264⟩ : DyadicInterval 40),(⟨-345009342336,-345009342272⟩ : DyadicInterval 40),(⟨721750197010,721750216340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82793507136,-82486225728⟩ : DyadicInterval 40),(⟨803366496480,803520156448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨261915032640,262274163968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-345110677632,-344486987008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e523_ok : ecellOkT e523 = true := by decide +kernel
theorem e523_pos {a z : ℝ} (ha1 : ((550863/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17241/64000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e523 e523_ok ha1 ha2 hz1 hz2 hz

-- box ['275007/1024000', '550863/2048000', '1999/2000', '1']  interval_lower 2149621219/1099511627776
noncomputable def e524 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1394798145568,0,true,261555784000,261555784064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨804225109984,0,false,-343863650176,-343863650112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1395253948974,0,true,261915032640,261915032704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨803769306578,0,false,-344486987072,-344486987008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1394650502309,0,true,261439391488,261439391552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨804372753243,0,false,-343661815424,-343661815360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589688021,0,true,78057472,78057536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433567531,0,false,-78063040,-78062976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622234,0,false,-5568,-5504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1394724317737,0,true,261497584384,261497584448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨804298937815,0,false,-343762719680,-343762719616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1395253957617,0,true,261915039424,261915039488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨803769297935,0,false,-344486998912,-344486998848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1019964014590,0,false,-82571959424,-82571959360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1020248680380,0,false,-82265135232,-82265135168⟩
    { al := (275007/1024000), au := (550863/2048000), zl := (1999/2000), zu := 1,
      A := ⟨295286517792,295742321198⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261555784000,261555784064⟩ : DyadicInterval 40),(⟨-343863650176,-343863650112⟩ : DyadicInterval 40),(⟨721981133859,721981153189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261915032640,261915032704⟩ : DyadicInterval 40),(⟨-344486987072,-344486987008⟩ : DyadicInterval 40),(⟨721855543437,721855562766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261439391488,261439391552⟩ : DyadicInterval 40),(⟨-343661815424,-343661815360⟩ : DyadicInterval 40),(⟨722021771264,722021790594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261915032640,261915032704⟩ : DyadicInterval 40),(⟨-344486987072,-344486987008⟩ : DyadicInterval 40),(⟨721855543437,721855562766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78060245⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78057472,78057536⟩ : DyadicInterval 40),(⟨-78063040,-78062976⟩ : DyadicInterval 40),(⟨762123380793,762123400123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,0⟩ : DyadicInterval 40),(⟨762123383616,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨295212689961,295742329841⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261497584384,261497584448⟩ : DyadicInterval 40),(⟨-343762719680,-343762719616⟩ : DyadicInterval 40),(⟨722001456942,722001476272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261915039424,261915039488⟩ : DyadicInterval 40),(⟨-344486998912,-344486998848⟩ : DyadicInterval 40),(⟨721855541077,721855560406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82571959424,-82265135168⟩ : DyadicInterval 40),(⟨803255951200,803409382592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨261555784000,261915032704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-344486987072,-343863650112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e524_ok : ecellOkT e524 = true := by decide +kernel
theorem e524_pos {a z : ℝ} (ha1 : ((275007/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((550863/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e524 e524_ok ha1 ha2 hz1 hz2 hz

-- box ['550863/2048000', '17241/64000', '1999/2000', '1']  interval_lower 271907973/137438953472
noncomputable def e525 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1395253948973,0,true,261915032640,261915032704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨803769306579,0,false,-344486987072,-344486987008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1395709752378,0,true,262274163904,262274163968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨803313503174,0,false,-345110677632,-345110677568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1395106077812,0,true,261798498496,261798498560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨803917177740,0,false,-344284726208,-344284726144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589821955,0,true,78191360,78191424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433433597,0,false,-78196992,-78196928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622215,0,false,-5568,-5504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1395180007195,0,true,261856762240,261856762304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨803843248357,0,false,-344385843520,-344385843456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1395709761018,0,true,262274170688,262274170752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨803313494534,0,false,-345110689408,-345110689344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1019718625210,0,false,-82836518720,-82836518656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1020003791406,0,false,-82529081280,-82529081216⟩
    { al := (550863/2048000), au := (17241/64000), zl := (1999/2000), zu := 1,
      A := ⟨295742321197,296198124602⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261915032640,261915032704⟩ : DyadicInterval 40),(⟨-344486987072,-344486987008⟩ : DyadicInterval 40),(⟨721855543437,721855562766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262274163904,262274163968⟩ : DyadicInterval 40),(⟨-345110677632,-345110677568⟩ : DyadicInterval 40),(⟨721729749377,721729768706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261798498496,261798498560⟩ : DyadicInterval 40),(⟨-344284726208,-344284726144⟩ : DyadicInterval 40),(⟨721896309664,721896328993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262274163904,262274163968⟩ : DyadicInterval 40),(⟨-345110677632,-345110677568⟩ : DyadicInterval 40),(⟨721729749377,721729768706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78194179⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78191360,78191424⟩ : DyadicInterval 40),(⟨-78196992,-78196928⟩ : DyadicInterval 40),(⟨762123380806,762123400136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,0⟩ : DyadicInterval 40),(⟨762123383616,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨295668379419,296198133242⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨261856762240,261856762304⟩ : DyadicInterval 40),(⟨-344385843520,-344385843456⟩ : DyadicInterval 40),(⟨721875930933,721875950263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262274170688,262274170752⟩ : DyadicInterval 40),(⟨-345110689408,-345110689344⟩ : DyadicInterval 40),(⟨721729746986,721729766316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-82836518720,-82529081216⟩ : DyadicInterval 40),(⟨803387924224,803541662240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨261915032640,262274163968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-345110677632,-344486987008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e525_ok : ecellOkT e525 = true := by decide +kernel
theorem e525_pos {a z : ℝ} (ha1 : ((550863/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17241/64000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e525 e525_ok ha1 ha2 hz1 hz2 hz

-- box ['17241/64000', '552561/2048000', '999/1000', '1999/2000']  interval_lower 1103615387/549755813888
noncomputable def e526 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1395709752377,0,true,262274163904,262274163968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨803313503175,0,false,-345110677632,-345110677568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1396165555782,0,true,262633177856,262633177920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨802857699770,0,false,-345734722112,-345734722048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1395413554252,0,true,262040800256,262040800320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨803609701300,0,false,-344705339904,-344705339840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1396017228819,0,true,262516360832,262516360896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨803006026733,0,false,-345531607488,-345531607424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589817009,0,true,78186432,78186496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433438543,0,false,-78192064,-78192000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099668279427,0,true,156640448,156640512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099354976125,0,false,-156662848,-156662784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605457,0,false,-22336,-22272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622216,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1395561650084,0,true,262157485696,262157485760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨803461605468,0,false,-344907985664,-344907985600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1396091401929,0,true,262574778496,262574778560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨802931853623,0,false,-345633173312,-345633173248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1019512871769,0,false,-83058394752,-83058394688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1019798404656,0,false,-82750499904,-82750499840⟩
    { al := (17241/64000), au := (552561/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨296198124601,296653928006⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262274163904,262274163968⟩ : DyadicInterval 40),(⟨-345110677632,-345110677568⟩ : DyadicInterval 40),(⟨721729749377,721729768706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262633177856,262633177920⟩ : DyadicInterval 40),(⟨-345734722112,-345734722048⟩ : DyadicInterval 40),(⟨721603751584,721603770913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262040800256,262040800320⟩ : DyadicInterval 40),(⟨-344705339904,-344705339840⟩ : DyadicInterval 40),(⟨721811518279,721811537609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262516360832,262516360896⟩ : DyadicInterval 40),(⟨-345531607488,-345531607424⟩ : DyadicInterval 40),(⟨721644776013,721644795343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78189233,156651651⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78186432,78186496⟩ : DyadicInterval 40),(⟨-78192064,-78192000⟩ : DyadicInterval 40),(⟨762123380807,762123400136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156640448,156640512⟩ : DyadicInterval 40),(⟨-156662848,-156662784⟩ : DyadicInterval 40),(⟨762123372432,762123391762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22336,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123414048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨296050022308,296579774153⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262157485696,262157485760⟩ : DyadicInterval 40),(⟨-344907985664,-344907985600⟩ : DyadicInterval 40),(⟨721770645491,721770664820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262574778496,262574778560⟩ : DyadicInterval 40),(⟨-345633173312,-345633173248⟩ : DyadicInterval 40),(⟨721624263828,721624283158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83058394752,-82750499840⟩ : DyadicInterval 40),(⟨803498633536,803652600256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨262274163904,262633177920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-345734722112,-345110677568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e526_ok : ecellOkT e526 = true := by decide +kernel
theorem e526_pos {a z : ℝ} (ha1 : ((17241/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((552561/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e526 e526_ok ha1 ha2 hz1 hz2 hz

-- box ['552561/2048000', '55341/204800', '999/1000', '1999/2000']  interval_lower 2233228597/1099511627776
noncomputable def e527 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1396165555781,0,true,262633177856,262633177920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨802857699771,0,false,-345734722112,-345734722048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1396621359186,0,true,262992074688,262992074752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨802401896366,0,false,-346359121024,-346359120960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1395868901852,0,true,262399531456,262399531520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨803154353700,0,false,-345328530304,-345328530240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1396472804321,0,true,262875116352,262875116416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨802550451231,0,false,-346155578752,-346155578688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589950988,0,true,78320384,78320448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433304564,0,false,-78326016,-78325952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099668547547,0,true,156908544,156908608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099354708005,0,false,-156931008,-156930944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605380,0,false,-22400,-22336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622197,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1396017225601,0,true,262516358336,262516358400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨803006029951,0,false,-345531603072,-345531603008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1396547091394,0,true,262933604672,262933604736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨802476164158,0,false,-346257358400,-346257358336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1019266849623,0,false,-83323753728,-83323753664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1019552883075,0,false,-83015244736,-83015244672⟩
    { al := (552561/2048000), au := (55341/204800), zl := (999/1000), zu := (1999/2000),
      A := ⟨296653928005,297109731410⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262633177856,262633177920⟩ : DyadicInterval 40),(⟨-345734722112,-345734722048⟩ : DyadicInterval 40),(⟨721603751584,721603770914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262992074688,262992074752⟩ : DyadicInterval 40),(⟨-346359121024,-346359120960⟩ : DyadicInterval 40),(⟨721477549976,721477569306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262399531456,262399531520⟩ : DyadicInterval 40),(⟨-345328530304,-345328530240⟩ : DyadicInterval 40),(⟨721685778799,721685798128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262875116352,262875116416⟩ : DyadicInterval 40),(⟨-346155578752,-346155578688⟩ : DyadicInterval 40),(⟨721518703828,721518723158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78323212,156919771⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78320384,78320448⟩ : DyadicInterval 40),(⟨-78326016,-78325952⟩ : DyadicInterval 40),(⟨762123380788,762123400117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156908544,156908608⟩ : DyadicInterval 40),(⟨-156931008,-156930944⟩ : DyadicInterval 40),(⟨762123372388,762123391718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22400,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123414080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨296505597825,297035463618⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262516358336,262516358400⟩ : DyadicInterval 40),(⟨-345531603072,-345531603008⟩ : DyadicInterval 40),(⟨721644776875,721644796204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262933604672,262933604736⟩ : DyadicInterval 40),(⟨-346257358400,-346257358336⟩ : DyadicInterval 40),(⟨721498126939,721498146268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83323753728,-83015244672⟩ : DyadicInterval 40),(⟨803631005952,803785279744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨262633177856,262992074752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-346359121024,-345734722048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e527_ok : ecellOkT e527 = true := by decide +kernel
theorem e527_pos {a z : ℝ} (ha1 : ((552561/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((55341/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e527 e527_ok ha1 ha2 hz1 hz2 hz

-- box ['17241/64000', '552561/2048000', '1999/2000', '1']  interval_lower 275133025/137438953472
noncomputable def e528 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1395709752377,0,true,262274163904,262274163968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨803313503175,0,false,-345110677632,-345110677568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1396165555782,0,true,262633177856,262633177920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨802857699770,0,false,-345734722112,-345734722048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1395561653314,0,true,262157488256,262157488320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨803461602238,0,false,-344907990080,-344907990016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589955958,0,true,78325376,78325440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433299594,0,false,-78331008,-78330944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622195,0,false,-5632,-5568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1395635696643,0,true,262215822720,262215822784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨803387558909,0,false,-345009320704,-345009320640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1396165564417,0,true,262633184640,262633184704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨802857691135,0,false,-345734733952,-345734733888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1019472857924,0,false,-83101549248,-83101549184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1019758524720,0,false,-82793497920,-82793497856⟩
    { al := (17241/64000), au := (552561/2048000), zl := (1999/2000), zu := 1,
      A := ⟨296198124601,296653928006⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262274163904,262274163968⟩ : DyadicInterval 40),(⟨-345110677632,-345110677568⟩ : DyadicInterval 40),(⟨721729749377,721729768706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262633177856,262633177920⟩ : DyadicInterval 40),(⟨-345734722112,-345734722048⟩ : DyadicInterval 40),(⟨721603751584,721603770913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262157488256,262157488320⟩ : DyadicInterval 40),(⟨-344907990080,-344907990016⟩ : DyadicInterval 40),(⟨721770644588,721770663918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262633177856,262633177920⟩ : DyadicInterval 40),(⟨-345734722112,-345734722048⟩ : DyadicInterval 40),(⟨721603751584,721603770913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78328182⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78325376,78325440⟩ : DyadicInterval 40),(⟨-78331008,-78330944⟩ : DyadicInterval 40),(⟨762123380787,762123400117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,0⟩ : DyadicInterval 40),(⟨762123383616,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨296124068867,296653936641⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262215822720,262215822784⟩ : DyadicInterval 40),(⟨-345009320704,-345009320640⟩ : DyadicInterval 40),(⟨721750201400,721750220730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262633184640,262633184704⟩ : DyadicInterval 40),(⟨-345734733952,-345734733888⟩ : DyadicInterval 40),(⟨721603749211,721603768540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83101549248,-82793497856⟩ : DyadicInterval 40),(⟨803520132544,803674177504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨262274163904,262633177920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-345734722112,-345110677568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e528_ok : ecellOkT e528 = true := by decide +kernel
theorem e528_pos {a z : ℝ} (ha1 : ((17241/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((552561/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e528 e528_ok ha1 ha2 hz1 hz2 hz

-- box ['552561/2048000', '55341/204800', '1999/2000', '1']  interval_lower 556756027/274877906944
noncomputable def e529 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1396165555781,0,true,262633177856,262633177920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨802857699771,0,false,-345734722112,-345734722048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1396621359186,0,true,262992074688,262992074752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨802401896366,0,false,-346359121024,-346359120960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1396017228816,0,true,262516360832,262516360896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨803006026736,0,false,-345531607488,-345531607424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590090029,0,true,78459392,78459456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433165523,0,false,-78465088,-78465024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622176,0,false,-5632,-5568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1396091386086,0,true,262574766016,262574766080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨802931869466,0,false,-345633151616,-345633151552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1396621367826,0,true,262992081472,262992081536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨802401887726,0,false,-346359132864,-346359132800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1019226712725,0,false,-83367051328,-83367051264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1019512880317,0,false,-83058385536,-83058385472⟩
    { al := (552561/2048000), au := (55341/204800), zl := (1999/2000), zu := 1,
      A := ⟨296653928005,297109731410⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262633177856,262633177920⟩ : DyadicInterval 40),(⟨-345734722112,-345734722048⟩ : DyadicInterval 40),(⟨721603751584,721603770914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262992074688,262992074752⟩ : DyadicInterval 40),(⟨-346359121024,-346359120960⟩ : DyadicInterval 40),(⟨721477549976,721477569306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262516360832,262516360896⟩ : DyadicInterval 40),(⟨-345531607488,-345531607424⟩ : DyadicInterval 40),(⟨721644776014,721644795344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262992074688,262992074752⟩ : DyadicInterval 40),(⟨-346359121024,-346359120960⟩ : DyadicInterval 40),(⟨721477549976,721477569306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78462253⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78459392,78459456⟩ : DyadicInterval 40),(⟨-78465088,-78465024⟩ : DyadicInterval 40),(⟨762123380800,762123400130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,0⟩ : DyadicInterval 40),(⟨762123383616,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨296579758310,297109740050⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262574766016,262574766080⟩ : DyadicInterval 40),(⟨-345633151616,-345633151552⟩ : DyadicInterval 40),(⟨721624268211,721624287540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262992081472,262992081536⟩ : DyadicInterval 40),(⟨-346359132864,-346359132800⟩ : DyadicInterval 40),(⟨721477547594,721477566923⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83367051328,-83058385472⟩ : DyadicInterval 40),(⟨803652576352,803806928544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨262633177856,262992074752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-346359121024,-345734722048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e529_ok : ecellOkT e529 = true := by decide +kernel
theorem e529_pos {a z : ℝ} (ha1 : ((552561/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((55341/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e529 e529_ok ha1 ha2 hz1 hz2 hz

-- box ['55341/204800', '554259/2048000', '1999/2000', '1']  interval_lower 1126572025/549755813888
noncomputable def e530 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1396621359185,0,true,262992074688,262992074752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨802401896367,0,false,-346359121024,-346359120960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1397077162591,0,true,263350854336,263350854400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨801946092961,0,false,-346983874688,-346983874624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1396472804319,0,true,262875116352,262875116416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨802550451233,0,false,-346155578752,-346155578688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590224170,0,true,78593536,78593600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433031382,0,false,-78599232,-78599168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622157,0,false,-5632,-5568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1396547075543,0,true,262933592192,262933592256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨802476180009,0,false,-346257336640,-346257336576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1397077171224,0,true,263350861184,263350861248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨801946084328,0,false,-346983886528,-346983886464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1018980189625,0,false,-83633025344,-83633025280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1019266858189,0,false,-83323744448,-83323744384⟩
    { al := (55341/204800), au := (554259/2048000), zl := (1999/2000), zu := 1,
      A := ⟨297109731409,297565534815⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262992074688,262992074752⟩ : DyadicInterval 40),(⟨-346359121024,-346359120960⟩ : DyadicInterval 40),(⟨721477549977,721477569306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263350854336,263350854400⟩ : DyadicInterval 40),(⟨-346983874688,-346983874624⟩ : DyadicInterval 40),(⟨721351144563,721351163893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262875116352,262875116416⟩ : DyadicInterval 40),(⟨-346155578752,-346155578688⟩ : DyadicInterval 40),(⟨721518703829,721518723158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263350854336,263350854400⟩ : DyadicInterval 40),(⟨-346983874688,-346983874624⟩ : DyadicInterval 40),(⟨721351144563,721351163893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78596394⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78593536,78593600⟩ : DyadicInterval 40),(⟨-78599232,-78599168⟩ : DyadicInterval 40),(⟨762123380781,762123400110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,0⟩ : DyadicInterval 40),(⟨762123383616,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨297035447767,297565543448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262933592192,262933592256⟩ : DyadicInterval 40),(⟨-346257336640,-346257336576⟩ : DyadicInterval 40),(⟨721498131315,721498150644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263350861184,263350861248⟩ : DyadicInterval 40),(⟨-346983886528,-346983886464⟩ : DyadicInterval 40),(⟨721351142135,721351161464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83633025344,-83323744384⟩ : DyadicInterval 40),(⟨803785255808,803939915552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨262992074688,263350854400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-346983874688,-346359120960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e530_ok : ecellOkT e530 = true := by decide +kernel
theorem e530_pos {a z : ℝ} (ha1 : ((55341/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((554259/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e530 e530_ok ha1 ha2 hz1 hz2 hz

-- box ['554259/2048000', '138777/512000', '1999/2000', '1']  interval_lower 2279423957/1099511627776
noncomputable def e531 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1397077162590,0,true,263350854336,263350854400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨801946092962,0,false,-346983874688,-346983874624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1397532965995,0,true,263709516992,263709517056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨801490289557,0,false,-347608983552,-347608983488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1396928379822,0,true,263233754816,263233754880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨802094875730,0,false,-346779904384,-346779904320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590358380,0,true,78727744,78727808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432897172,0,false,-78733440,-78733376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622138,0,false,-5696,-5632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1397002764986,0,true,263292301248,263292301312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨802020490566,0,false,-346881876288,-346881876224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1397532974630,0,true,263709523840,263709523904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨801490280922,0,false,-347608995392,-347608995328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1018733288614,0,false,-83899471552,-83899471488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1019020458349,0,false,-83589574976,-83589574912⟩
    { al := (554259/2048000), au := (138777/512000), zl := (1999/2000), zu := 1,
      A := ⟨297565534814,298021338219⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263350854336,263350854400⟩ : DyadicInterval 40),(⟨-346983874688,-346983874624⟩ : DyadicInterval 40),(⟨721351144564,721351163893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263709516992,263709517056⟩ : DyadicInterval 40),(⟨-347608983552,-347608983488⟩ : DyadicInterval 40),(⟨721224535239,721224554569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263233754816,263233754880⟩ : DyadicInterval 40),(⟨-346779904384,-346779904320⟩ : DyadicInterval 40),(⟨721392428073,721392447403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263709516992,263709517056⟩ : DyadicInterval 40),(⟨-347608983552,-347608983488⟩ : DyadicInterval 40),(⟨721224535239,721224554569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78730604⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78727744,78727808⟩ : DyadicInterval 40),(⟨-78733440,-78733376⟩ : DyadicInterval 40),(⟨762123380762,762123400091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,0⟩ : DyadicInterval 40),(⟨762123383616,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨297491137210,298021346854⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263292301248,263292301312⟩ : DyadicInterval 40),(⟨-346881876288,-346881876224⟩ : DyadicInterval 40),(⟨721371790758,721371810087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263709523840,263709523904⟩ : DyadicInterval 40),(⟨-347608995392,-347608995328⟩ : DyadicInterval 40),(⟨721224532802,721224552132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83899471552,-83589574912⟩ : DyadicInterval 40),(⟨803918171072,804073138656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨263350854336,263709517056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-347608983552,-346983874624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e531_ok : ecellOkT e531 = true := by decide +kernel
theorem e531_pos {a z : ℝ} (ha1 : ((554259/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((138777/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e531 e531_ok ha1 ha2 hz1 hz2 hz

-- box ['1018731/1024000', '2038311/2048000', '1999/2000', '1']  interval_lower 2105715853887811/549755813888
noncomputable def e532 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2193365709881,0,true,759290965760,759290983872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨5657545671,7,false,-5794020920896,-5794020785984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2193821513286,0,true,759519431552,759519449728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨5201742266,7,false,-5886376105024,-5886375969984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2192818782839,0,true,759016762688,759016780672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨6204472713,7,false,-5692557695296,-5692557560384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1110888850153,0,true,11318762240,11318762304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1088134405399,0,false,-11436494656,-11436494592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393901700,0,false,-117732416,-117732352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2193093294328,0,true,759154398144,759154416256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨5929961224,7,false,-5742313634688,-5742313499776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2193821527480,0,true,759519438656,759519456896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨5201728072,7,false,-5886379105216,-5886378970240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨10378847059,6,false,-5126859647424,-5126859531648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨11827940577,6,false,-4983159217216,-4983159101568⟩
    { al := (1018731/1024000), au := (2038311/2048000), zl := (1999/2000), zu := 1,
      A := ⟨1093854082105,1094309885510⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759290965760,759290983872⟩ : DyadicInterval 40),(⟨-5794020920896,-5794020785984⟩ : DyadicInterval 40),(⟨19692458199,19692495877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759519431552,759519449728⟩ : DyadicInterval 40),(⟨-5886376105024,-5886375969984⟩ : DyadicInterval 40),(⟨18324656718,18324694436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759016762688,759016780672⟩ : DyadicInterval 40),(⟨-5692557695296,-5692557560384⟩ : DyadicInterval 40),(⟨21309510463,21309548043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759519431552,759519449728⟩ : DyadicInterval 40),(⟨-5886376105024,-5886375969984⟩ : DyadicInterval 40),(⟨18324656718,18324694436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11377222377⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11318762240,11318762304⟩ : DyadicInterval 40),(⟨-11436494656,-11436494592⟩ : DyadicInterval 40),(⟨762064519482,762064538812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-117732416,0⟩ : DyadicInterval 40),(⟨762123383616,762182269088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1093581666552,1094309899704⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759154398144,759154416256⟩ : DyadicInterval 40),(⟨-5742313634688,-5742313499776⟩ : DyadicInterval 40),(⟨20501047815,20501085508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759519438656,759519456896⟩ : DyadicInterval 40),(⟨-5886379105216,-5886378970240⟩ : DyadicInterval 40),(⟨18324613767,18324651549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5126859647424,-4983159101568⟩ : DyadicInterval 40),(⟨3253702934400,3325553226592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨759290965760,759519449728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5886376105024,-5794020785984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e532_ok : ecellOkT e532 = true := by decide +kernel
theorem e532_pos {a z : ℝ} (ha1 : ((1018731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2038311/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e532 e532_ok ha1 ha2 hz1 hz2 hz

-- box ['2038311/2048000', '50979/51200', '1999/2000', '1']  interval_lower 4486644567440407/1099511627776
noncomputable def e533 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2193821513285,0,true,759519431552,759519449728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨5201742267,7,false,-5886376104768,-5886375969792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2194277316690,0,true,759747849920,759747868160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨4745938862,7,false,-5987206099712,-5987205963200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2193274358342,0,true,759245171200,759245189312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨5748897210,7,false,-5776409080320,-5776408945408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1111826091937,0,true,12246014144,12246014208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1087197163615,0,false,-12383944064,-12383944000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099373706517,0,false,-137929920,-137929856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2193549058261,0,true,759382872576,759382890688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨5474197291,7,false,-5830243803392,-5830243668480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2194277330824,0,true,759747856960,759747875264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨4745924728,7,false,-5987209374208,-5987209237696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨9471364177,6,false,-5227461498176,-5227461380864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨10921139904,6,false,-5070860911616,-5070860795968⟩
    { al := (2038311/2048000), au := (50979/51200), zl := (1999/2000), zu := 1,
      A := ⟨1094309885509,1094765688914⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759519431552,759519449728⟩ : DyadicInterval 40),(⟨-5886376104768,-5886375969792⟩ : DyadicInterval 40),(⟨18324656721,18324694439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759747849920,759747868160⟩ : DyadicInterval 40),(⟨-5987206099712,-5987205963200⟩ : DyadicInterval 40),(⟨16936812298,16936850059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759245171200,759245189312⟩ : DyadicInterval 40),(⟨-5776409080320,-5776408945408⟩ : DyadicInterval 40),(⟨19964327306,19964364989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759747849920,759747868160⟩ : DyadicInterval 40),(⟨-5987206099712,-5987205963200⟩ : DyadicInterval 40),(⟨16936812298,16936850059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,12314464161⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨12246014144,12246014208⟩ : DyadicInterval 40),(⟨-12383944064,-12383944000⟩ : DyadicInterval 40),(⟨762054421485,762054440815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-137929920,0⟩ : DyadicInterval 40),(⟨762123383616,762192367840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1094037430485,1094765703048⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759382872576,759382890688⟩ : DyadicInterval 40),(⟨-5830243803392,-5830243668480⟩ : DyadicInterval 40),(⟨19144555853,19144593521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759747856960,759747875264⟩ : DyadicInterval 40),(⟨-5987209374208,-5987209237696⟩ : DyadicInterval 40),(⟨16936768911,16936806736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5227461498176,-5070860795968⟩ : DyadicInterval 40),(⟨3297553781600,3375854151968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨759519431552,759747868160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5987206099712,-5886375969792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e533_ok : ecellOkT e533 = true := by decide +kernel
theorem e533_pos {a z : ℝ} (ha1 : ((2038311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50979/51200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e533 e533_ok ha1 ha2 hz1 hz2 hz

-- box ['50979/51200', '2040009/2048000', '999/1000', '1999/2000']  interval_lower 7016673851131459/1099511627776
noncomputable def e534 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2194277316689,0,true,759747849920,759747868160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨4745938863,7,false,-5987206099456,-5987205963008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2194733120095,0,true,759976220800,759976239168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨4290135457,8,false,-6098224870144,-6098224715968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2193182550999,0,true,759199146240,759199164352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨5840704553,7,false,-5758989093888,-5758988958976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2194185509350,0,true,759701845952,759701864256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨4837746202,7,false,-5966139812992,-5966139677120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1110733051149,0,true,11164548032,11164548096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1088290204403,0,false,-11279077952,-11279077888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1124992443429,0,true,25190044672,25190044736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1074030812123,0,false,-25780712768,-25780712704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098921118362,0,false,-590668096,-590668032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397103892,0,false,-114529856,-114529792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2193734608196,0,true,759475875136,759475893312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨5288647356,7,false,-5868158413056,-5868158278080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2194460655915,0,true,759839713920,759839732288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨4562599637,7,false,-6030523253056,-6030523113664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨9106266035,6,false,-5270683520256,-5270683399936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨10551856336,6,false,-5108682518720,-5108682403008⟩
    { al := (50979/51200), au := (2040009/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨1094765688913,1095221492319⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759747849920,759747868160⟩ : DyadicInterval 40),(⟨-5987206099456,-5987205963008⟩ : DyadicInterval 40),(⟨16936812301,16936850061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759976220800,759976239168⟩ : DyadicInterval 40),(⟨-6098224870144,-6098224715968⟩ : DyadicInterval 40),(⟨15526998896,15527036794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759199146240,759199164352⟩ : DyadicInterval 40),(⟨-5758989093888,-5758988958976⟩ : DyadicInterval 40),(⟨20236819734,20236857422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759701845952,759701864256⟩ : DyadicInterval 40),(⟨-5966139812992,-5966139677120⟩ : DyadicInterval 40),(⟨17218049724,17218087551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11221423373,25480815653⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11164548032,11164548096⟩ : DyadicInterval 40),(⟨-11279077952,-11279077888⟩ : DyadicInterval 40),(⟨762066120650,762066139980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25190044672,25190044736⟩ : DyadicInterval 40),(⟨-25780712768,-25780712704⟩ : DyadicInterval 40),(⟨761828102438,761828121768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-590668096,-114529792⟩ : DyadicInterval 40),(⟨762180648512,762418736928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1094222980420,1094949028139⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759475875136,759475893312⟩ : DyadicInterval 40),(⟨-5868158413056,-5868158278080⟩ : DyadicInterval 40),(⟨18586939715,18586977437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759839713920,759839732288⟩ : DyadicInterval 40),(⟨-6030523253056,-6030523113664⟩ : DyadicInterval 40),(⟨16372500537,16372538422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5270683520256,-5108682403008⟩ : DyadicInterval 40),(⟨3316464585120,3397465163008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨759747849920,759976239168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6098224870144,-5987205963008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e534_ok : ecellOkT e534 = true := by decide +kernel
theorem e534_pos {a z : ℝ} (ha1 : ((50979/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2040009/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e534 e534_ok ha1 ha2 hz1 hz2 hz

-- box ['2040009/2048000', '1020429/1024000', '999/1000', '1999/2000']  interval_lower 7908066724359557/1099511627776
noncomputable def e535 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2194733120094,0,true,759976220800,759976239168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨4290135458,8,false,-6098224869888,-6098224715712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2195188923499,0,true,760204544256,760204562752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨3834332053,8,false,-6221725379776,-6221725225600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2193637898601,0,true,759427402688,759427420864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨5385356951,7,false,-5848234075200,-5848233940288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2194641084853,0,true,759930112256,759930130624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨4382170699,7,false,-6074886753216,-6074886606336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1111640961916,0,true,12062919360,12062919424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1087382293636,0,false,-12196733056,-12196732992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1127420455955,0,true,27560506176,27560506240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1071602799597,0,false,-28269142464,-28269142400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098803219905,0,false,-708636224,-708636160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099377822237,0,false,-133813696,-133813632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2194190557111,0,true,759704375424,759704393728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨4832698441,7,false,-5967287655232,-5967287519360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2194916469583,0,true,760068070912,760068089344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨4106785969,8,false,-6146248885568,-6146248731392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨8198232681,7,false,-5386180795520,-5386180660608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨9644155657,6,false,-5207583260672,-5207583144000⟩
    { al := (2040009/2048000), au := (1020429/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨1095221492318,1095677295723⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759976220800,759976239168⟩ : DyadicInterval 40),(⟨-6098224869888,-6098224715712⟩ : DyadicInterval 40),(⟨15526998899,15527036797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760204544256,760204562752⟩ : DyadicInterval 40),(⟨-6221725379776,-6221725225600⟩ : DyadicInterval 40),(⟨14092879101,14092917099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759427402688,759427420864⟩ : DyadicInterval 40),(⟨-5848234075200,-5848233940288⟩ : DyadicInterval 40),(⟨18877972173,18878009901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759930112256,759930130624⟩ : DyadicInterval 40),(⟨-6074886753216,-6074886606336⟩ : DyadicInterval 40),(⟨15813542619,15813580508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨12129334140,27908828179⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨12062919360,12062919424⟩ : DyadicInterval 40),(⟨-12196733056,-12196732992⟩ : DyadicInterval 40),(⟨762056479431,762056498761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27560506176,27560506240⟩ : DyadicInterval 40),(⟨-28269142464,-28269142400⟩ : DyadicInterval 40),(⟨761769141625,761769160955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-708636224,-133813632⟩ : DyadicInterval 40),(⟨762190290432,762477720992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1094678929335,1095404841807⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759704375424,759704393728⟩ : DyadicInterval 40),(⟨-5967287655232,-5967287519360⟩ : DyadicInterval 40),(⟨17202609501,17202647329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760068070912,760068089344⟩ : DyadicInterval 40),(⟨-6146248885568,-6146248731392⟩ : DyadicInterval 40),(⟨14953186527,14953224477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5386180795520,-5207583144000⟩ : DyadicInterval 40),(⟨3365914955616,3455213800640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨759976220800,760204562752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6221725379776,-6098224715712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e535_ok : ecellOkT e535 = true := by decide +kernel
theorem e535_pos {a z : ℝ} (ha1 : ((2040009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1020429/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e535 e535_ok ha1 ha2 hz1 hz2 hz

-- box ['50979/51200', '2040009/2048000', '1999/2000', '1']  interval_lower 4645284667291673/1099511627776
noncomputable def e536 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2194277316689,0,true,759747849920,759747868160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨4745938863,7,false,-5987206099456,-5987205963008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2194733120095,0,true,759976220800,759976239168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨4290135457,8,false,-6098224870144,-6098224715968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2193729933844,0,true,759473532288,759473550464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨5293321708,7,false,-5867187042880,-5867186907904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1112949575635,0,true,13356493248,13356493312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1086073679917,0,false,-13520740736,-13520740672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099347392639,0,false,-164247424,-164247360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2194004834738,0,true,759611305792,759611324032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨5018420814,7,false,-5925824730048,-5925824594816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2194733134169,0,true,759976227840,759976246208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨4290121383,8,false,-6098228477184,-6098228323008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨8563503387,7,false,-5338252230144,-5338252095232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨10013936416,6,false,-5166213405056,-5166213289088⟩
    { al := (50979/51200), au := (2040009/2048000), zl := (1999/2000), zu := 1,
      A := ⟨1094765688913,1095221492319⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759747849920,759747868160⟩ : DyadicInterval 40),(⟨-5987206099456,-5987205963008⟩ : DyadicInterval 40),(⟨16936812301,16936850061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759976220800,759976239168⟩ : DyadicInterval 40),(⟨-6098224870144,-6098224715968⟩ : DyadicInterval 40),(⟨15526998896,15527036794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759473532288,759473550464⟩ : DyadicInterval 40),(⟨-5867187042880,-5867186907904⟩ : DyadicInterval 40),(⟨18601026740,18601064463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759976220800,759976239168⟩ : DyadicInterval 40),(⟨-6098224870144,-6098224715968⟩ : DyadicInterval 40),(⟨15526998896,15527036794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,13437947859⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨13356493248,13356493312⟩ : DyadicInterval 40),(⟨-13520740736,-13520740672⟩ : DyadicInterval 40),(⟨762041263980,762041283310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-164247424,0⟩ : DyadicInterval 40),(⟨762123383616,762205526592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1094493206962,1095221506393⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759611305792,759611324032⟩ : DyadicInterval 40),(⟨-5925824730048,-5925824594816⟩ : DyadicInterval 40),(⟨17768983621,17769021393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759976227840,759976246208⟩ : DyadicInterval 40),(⟨-6098228477184,-6098228323008⟩ : DyadicInterval 40),(⟨15526955013,15526992912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5338252230144,-5166213289088⟩ : DyadicInterval 40),(⟨3345230028160,3431249517952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨759747849920,759976239168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6098224870144,-5987205963008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e536_ok : ecellOkT e536 = true := by decide +kernel
theorem e536_pos {a z : ℝ} (ha1 : ((50979/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2040009/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e536 e536_ok ha1 ha2 hz1 hz2 hz

-- box ['2040009/2048000', '1020429/1024000', '1999/2000', '1']  interval_lower 2258203508656001/549755813888
noncomputable def e537 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2194733120094,0,true,759976220800,759976239168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨4290135458,8,false,-6098224869888,-6098224715712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2195188923499,0,true,760204544256,760204562752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨3834332053,8,false,-6221725379776,-6221725225600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2194185509347,0,true,759701845952,759701864256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨4837746205,7,false,-5966139812288,-5966139676480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1114322866935,0,true,14712366848,14712366912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1084700388617,0,false,-14911903424,-14911903360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099312109371,0,false,-199536512,-199536448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2194460627325,0,true,759839699648,759839717952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨4562628227,7,false,-6030516363328,-6030516224000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2195188937504,0,true,760204551296,760204569728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨3834318048,8,false,-6221729395776,-6221729241600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨7655264709,7,false,-5461524825408,-5461524690496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨9106322979,6,false,-5270676644736,-5270676524416⟩
    { al := (2040009/2048000), au := (1020429/1024000), zl := (1999/2000), zu := 1,
      A := ⟨1095221492318,1095677295723⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759976220800,759976239168⟩ : DyadicInterval 40),(⟨-6098224869888,-6098224715712⟩ : DyadicInterval 40),(⟨15526998899,15527036797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760204544256,760204562752⟩ : DyadicInterval 40),(⟨-6221725379776,-6221725225600⟩ : DyadicInterval 40),(⟨14092879101,14092917099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759701845952,759701864256⟩ : DyadicInterval 40),(⟨-5966139812288,-5966139676480⟩ : DyadicInterval 40),(⟨17218049731,17218087559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760204544256,760204562752⟩ : DyadicInterval 40),(⟨-6221725379776,-6221725225600⟩ : DyadicInterval 40),(⟨14092879101,14092917099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,14811239159⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨14712366848,14712366912⟩ : DyadicInterval 40),(⟨-14911903424,-14911903360⟩ : DyadicInterval 40),(⟨762023621366,762023640695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-199536512,0⟩ : DyadicInterval 40),(⟨762123383616,762223171136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1094948999549,1095677309728⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759839699648,759839717952⟩ : DyadicInterval 40),(⟨-6030516363328,-6030516224000⟩ : DyadicInterval 40),(⟨16372588831,16372626652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760204551296,760204569728⟩ : DyadicInterval 40),(⟨-6221729395776,-6221729241600⟩ : DyadicInterval 40),(⟨14092834674,14092872608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5461524825408,-5270676524416⟩ : DyadicInterval 40),(⟨3397461645824,3492885815584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨759976220800,760204562752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6221725379776,-6098224715712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e537_ok : ecellOkT e537 = true := by decide +kernel
theorem e537_pos {a z : ℝ} (ha1 : ((2040009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1020429/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e537 e537_ok ha1 ha2 hz1 hz2 hz

-- box ['1020429/1024000', '2041707/2048000', '999/1000', '1999/2000']  interval_lower 8801625789814763/1099511627776
noncomputable def e538 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2195188923498,0,true,760204544256,760204562752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨3834332054,8,false,-6221725379520,-6221725225344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2195644726903,0,true,760432820352,760432838912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨3378528649,8,false,-6360874012864,-6360873858688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2194093246202,0,true,759655611712,759655629952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨4930009350,7,false,-5945367912512,-5945367777088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2195096660355,0,true,760158331136,760158349632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨3926595197,8,false,-6195581808064,-6195581653888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1112725957504,0,true,13135552960,13135553024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1086297298048,0,false,-13294379072,-13294379008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1130415064026,0,true,30477112192,30477112256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1068608191526,0,false,-31346043328,-31346043264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098643039988,0,false,-868931072,-868931008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099352813167,0,false,-158826112,-158826048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2194646578566,0,true,759932864576,759932882944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨4376676986,7,false,-6076266022272,-6076265875008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2195372312080,0,true,760296394880,760296413376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨3650943472,8,false,-6275612036352,-6275611882176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨7289763936,7,false,-5515315622272,-5515315487360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨8735932327,6,false,-5316333139008,-5316333010432⟩
    { al := (1020429/1024000), au := (2041707/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨1095677295722,1096133099127⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760204544256,760204562752⟩ : DyadicInterval 40),(⟨-6221725379520,-6221725225344⟩ : DyadicInterval 40),(⟨14092879104,14092917102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760432820352,760432838912⟩ : DyadicInterval 40),(⟨-6360874012864,-6360873858688⟩ : DyadicInterval 40),(⟨12631556189,12631594223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759655611712,759655629952⟩ : DyadicInterval 40),(⟨-5945367912512,-5945367777088⟩ : DyadicInterval 40),(⟨17499803918,17499841686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760158331136,760158349632⟩ : DyadicInterval 40),(⟨-6195581808064,-6195581653888⟩ : DyadicInterval 40),(⟨14385264293,14385302296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨13214329728,30903436250⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨13135552960,13135553024⟩ : DyadicInterval 40),(⟨-13294379072,-13294379008⟩ : DyadicInterval 40),(⟨762043974350,762043993680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30477112192,30477112256⟩ : DyadicInterval 40),(⟨-31346043328,-31346043264⟩ : DyadicInterval 40),(⟨761689032502,761689051832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-868931072,-158826048⟩ : DyadicInterval 40),(⟨762202796640,762557868416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1095134950790,1095860684304⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759932864576,759932882944⟩ : DyadicInterval 40),(⟨-6076266022272,-6076265875008⟩ : DyadicInterval 40),(⟨15796465820,15796503710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760296394880,760296413376⟩ : DyadicInterval 40),(⟨-6275612036352,-6275611882176⟩ : DyadicInterval 40),(⟨13508385339,13508423325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5515315622272,-5316333010432⟩ : DyadicInterval 40),(⟨3420289888832,3519781214016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨760204544256,760432838912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6360874012864,-6221725225344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e538_ok : ecellOkT e538 = true := by decide +kernel
theorem e538_pos {a z : ℝ} (ha1 : ((1020429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2041707/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e538 e538_ok ha1 ha2 hz1 hz2 hz

-- box ['2041707/2048000', '510639/512000', '999/1000', '1999/2000']  interval_lower 1181033870294315/137438953472
noncomputable def e539 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2195644726902,0,true,760432820352,760432838912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨3378528650,8,false,-6360874012544,-6360873858368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196100530308,0,true,760661049024,760661067712⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2922725244,8,false,-6520219438144,-6520219283968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2194548593802,0,true,759883773440,759883791744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨4474661750,7,false,-6051921725184,-6051921583040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2195552235858,0,true,760386502720,760386521216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨3471019694,8,false,-6331178285248,-6331178131072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1114047313118,0,true,14440441984,14440442048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1084975942434,0,false,-14632622464,-14632622400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1134208043833,0,true,34160223360,34160223424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1064815211719,0,false,-35255656192,-35255656128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098416740503,0,false,-1095432832,-1095432768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099319464144,0,false,-192180480,-192180416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2195102696946,0,true,760161354880,760161373312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨3920558606,8,false,-6197273454080,-6197273299904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2195828195196,0,true,760524691840,760524710400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨3195060356,8,false,-6422264502848,-6422264348672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨6380836216,7,false,-5661739791936,-5661739657024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨7827137570,7,false,-5437112079936,-5437111945024⟩
    { al := (2041707/2048000), au := (510639/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨1096133099126,1096588902532⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760432820352,760432838912⟩ : DyadicInterval 40),(⟨-6360874012544,-6360873858368⟩ : DyadicInterval 40),(⟨12631556191,12631594225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661049024,760661067712⟩ : DyadicInterval 40),(⟨-6520219438144,-6520219283968⟩ : DyadicInterval 40),(⟨11139345352,11139383485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759883773440,759883791744⟩ : DyadicInterval 40),(⟨-6051921725184,-6051921583040⟩ : DyadicInterval 40),(⟨16100529850,16100567671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760386502720,760386521216⟩ : DyadicInterval 40),(⟨-6331178285248,-6331178131072⟩ : DyadicInterval 40),(⟨12930450511,12930488486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨14535685342,34696416057⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨14440441984,14440442048⟩ : DyadicInterval 40),(⟨-14632622464,-14632622400⟩ : DyadicInterval 40),(⟨762027298963,762027318292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34160223360,34160223424⟩ : DyadicInterval 40),(⟨-35255656192,-35255656128⟩ : DyadicInterval 40),(⟨761575849050,761575868380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1095432832,-192180416⟩ : DyadicInterval 40),(⟨762219473824,762671119296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1095591069170,1096316567420⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760161354880,760161373312⟩ : DyadicInterval 40),(⟨-6197273454080,-6197273299904⟩ : DyadicInterval 40),(⟨14366167610,14366205550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760524691840,760524710400⟩ : DyadicInterval 40),(⟨-6422264502848,-6422264348672⟩ : DyadicInterval 40),(⟨12034872337,12034910359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5661739791936,-5437111945024⟩ : DyadicInterval 40),(⟨3480679356128,3592993298848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨760432820352,760661067712⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6520219438144,-6360873858368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e539_ok : ecellOkT e539 = true := by decide +kernel
theorem e539_pos {a z : ℝ} (ha1 : ((2041707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((510639/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e539 e539_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B008

end


