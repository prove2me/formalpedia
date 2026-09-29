-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B010__2_q00
-- name    : CK_CKLaneC2R_EpCells_B010__2_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:53:27.30188+00:00
-- url     : https://prove2.me/theorems/3832e40c-cd9c-41c1-9604-7cf0895a9aed
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B010 (+1 modules: CKLaneC2R/EpCells/B011) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B010 =====
section

namespace CKLaneC2R.EpCells.B010

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['700149/4096000', '350499/2048000', '3999/4000', '1']  interval_lower 285595/137438953472
noncomputable def e600 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443858,0,true,173505591808,173505591872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811694,0,false,-206110596416,-206110596352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345562,0,true,173700206848,173700206912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909990,0,false,-206385520768,-206385520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287409457653,0,true,173465464000,173465464064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911613797899,0,false,-206053924160,-206053924096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535659876,0,true,24031808,24031872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487595676,0,false,-24032384,-24032320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627250,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1287432945931,0,true,173485523968,173485524032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨911590309621,0,false,-206082254080,-206082254016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684354045,0,true,173700214080,173700214144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨911338901507,0,false,-206385531008,-206385530944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067307352698,0,false,-32685316864,-32685316800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067393348238,0,false,-32596730112,-32596730048⟩
    { al := (700149/4096000), au := (350499/2048000), zl := (3999/4000), zu := 1,
      A := ⟨187944816082,188172717786⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173465464000,173465464064⟩ : DyadicInterval 40),(⟨-206053924160,-206053924096⟩ : DyadicInterval 40),(⟨745989184668,745989203998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24032100⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24031808,24031872⟩ : DyadicInterval 40),(⟨-24032384,-24032320⟩ : DyadicInterval 40),(⟨762123383314,762123402643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨187921318155,188172726269⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173485523968,173485524032⟩ : DyadicInterval 40),(⟨-206082254080,-206082254016⟩ : DyadicInterval 40),(⟨745985130668,745985149998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700214080,173700214144⟩ : DyadicInterval 40),(⟨-206385531008,-206385530944⟩ : DyadicInterval 40),(⟨745941706182,745941725511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32685316864,-32596730048⟩ : DyadicInterval 40),(⟨778421748640,778466061312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨173505591808,173700206912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206385520768,-206110596352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e600_ok : ecellOkT e600 = true := by decide +kernel
theorem e600_pos {a z : ℝ} (ha1 : ((700149/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((350499/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e600 e600_ok ha1 ha2 hz1 hz2 hz

-- box ['350499/2048000', '701847/4096000', '1999/2000', '3999/4000']  interval_lower 165789/34359738368
noncomputable def e601 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345561,0,true,173700206848,173700206912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909991,0,false,-206385520768,-206385520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247264,0,true,173894787456,173894787520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008288,0,false,-206660513856,-206660513792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287590259202,0,true,173619866624,173619866688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911432996350,0,false,-206272013376,-206272013312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287865147110,0,true,173854576576,173854576640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911158108442,0,false,-206603675776,-206603675712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535659099,0,true,24031040,24031104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487596453,0,false,-24031616,-24031552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559752209,0,true,48123328,48123392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463503343,0,false,-48125504,-48125440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625669,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627251,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287637297735,0,true,173660033536,173660033600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911385957817,0,false,-206328760000,-206328759936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287888705734,0,true,173874689472,173874689536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911134549818,0,false,-206632104768,-206632104704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067237368365,0,false,-32757415232,-32757415168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067323457317,0,false,-32668726464,-32668726400⟩
    { al := (350499/2048000), au := (701847/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨188172717785,188400619488⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173619866624,173619866688⟩ : DyadicInterval 40),(⟨-206272013376,-206272013312⟩ : DyadicInterval 40),(⟨745957965671,745957985001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173854576576,173854576640⟩ : DyadicInterval 40),(⟨-206603675776,-206603675712⟩ : DyadicInterval 40),(⟨745910442042,745910461371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24031323,48124433⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24031040,24031104⟩ : DyadicInterval 40),(⟨-24031616,-24031552⟩ : DyadicInterval 40),(⟨762123383314,762123402643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48123328,48123392⟩ : DyadicInterval 40),(⟨-48125504,-48125440⟩ : DyadicInterval 40),(⟨762123382533,762123401862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188125669959,188377077958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173660033536,173660033600⟩ : DyadicInterval 40),(⟨-206328760000,-206328759936⟩ : DyadicInterval 40),(⟨745949838474,745949857804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173874689472,173874689536⟩ : DyadicInterval 40),(⟨-206632104768,-206632104704⟩ : DyadicInterval 40),(⟨745906365865,745906385194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32757415232,-32668726400⟩ : DyadicInterval 40),(⟨778457746816,778502110496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173700206848,173894787520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206660513856,-206385520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e601_ok : ecellOkT e601 = true := by decide +kernel
theorem e601_pos {a z : ℝ} (ha1 : ((350499/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((701847/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e601 e601_ok ha1 ha2 hz1 hz2 hz

-- box ['701847/4096000', '87837/512000', '1999/2000', '3999/4000']  interval_lower 1958837/274877906944
noncomputable def e602 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247263,0,true,173894787456,173894787520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008289,0,false,-206660513856,-206660513792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148966,0,true,174089333632,174089333696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106586,0,false,-206935575744,-206935575680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287818046953,0,true,173814364160,173814364224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911205208599,0,false,-206546840576,-206546840512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288092991836,0,true,174049081216,174049081280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910930263716,0,false,-206878654656,-206878654592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535689475,0,true,24061376,24061440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487566077,0,false,-24062016,-24061952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559812972,0,true,48184128,48184192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463442580,0,false,-48186304,-48186240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625664,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627250,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287865142460,0,true,173854572608,173854572672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911158113092,0,false,-206603670144,-206603670080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288116578948,0,true,174069214912,174069214976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910906676604,0,false,-206907125120,-206907125056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067159239035,0,false,-32837910208,-32837910144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067245441956,0,false,-32749097536,-32749097472⟩
    { al := (701847/4096000), au := (87837/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨188400619487,188628521190⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173814364160,173814364224⟩ : DyadicInterval 40),(⟨-206546840576,-206546840512⟩ : DyadicInterval 40),(⟨745918589927,745918609256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174049081216,174049081280⟩ : DyadicInterval 40),(⟨-206878654656,-206878654592⟩ : DyadicInterval 40),(⟨745870997763,745871017092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24061699,48185196⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24061376,24061440⟩ : DyadicInterval 40),(⟨-24062016,-24061952⟩ : DyadicInterval 40),(⟨762123383345,762123402674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48184128,48184192⟩ : DyadicInterval 40),(⟨-48186304,-48186240⟩ : DyadicInterval 40),(⟨762123382528,762123401857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188353514684,188604951172⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173854572608,173854572672⟩ : DyadicInterval 40),(⟨-206603670144,-206603670080⟩ : DyadicInterval 40),(⟨745910442837,745910462166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174069214912,174069214976⟩ : DyadicInterval 40),(⟨-206907125120,-206907125056⟩ : DyadicInterval 40),(⟨745866911586,745866930916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32837910208,-32749097472⟩ : DyadicInterval 40),(⟨778497932352,778542357984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173894787456,174089333696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206935575744,-206660513792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e602_ok : ecellOkT e602 = true := by decide +kernel
theorem e602_pos {a z : ℝ} (ha1 : ((701847/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87837/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e602 e602_ok ha1 ha2 hz1 hz2 hz

-- box ['350499/2048000', '701847/4096000', '3999/4000', '1']  interval_lower 1199963/274877906944
noncomputable def e603 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345561,0,true,173700206848,173700206912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909991,0,false,-206385520768,-206385520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247264,0,true,173894787456,173894787520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008288,0,false,-206660513856,-206660513792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287637302381,0,true,173660037504,173660037568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911385953171,0,false,-206328765568,-206328765504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535690253,0,true,24062208,24062272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487565299,0,false,-24062784,-24062720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627249,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1287660819142,0,true,173680118208,173680118272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨911362436410,0,false,-206357136960,-206357136896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912255748,0,true,173894794688,173894794752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨911110999804,0,false,-206660524096,-206660524032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067229298309,0,false,-32765729344,-32765729280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067315407821,0,false,-32677018752,-32677018688⟩
    { al := (350499/2048000), au := (701847/4096000), zl := (3999/4000), zu := 1,
      A := ⟨188172717785,188400619488⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173660037504,173660037568⟩ : DyadicInterval 40),(⟨-206328765568,-206328765504⟩ : DyadicInterval 40),(⟨745949837655,745949856985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24062477⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24062208,24062272⟩ : DyadicInterval 40),(⟨-24062784,-24062720⟩ : DyadicInterval 40),(⟨762123383313,762123402642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨188149191366,188400627972⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173680118208,173680118272⟩ : DyadicInterval 40),(⟨-206357136960,-206357136896⟩ : DyadicInterval 40),(⟨745945773751,745945793080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894794688,173894794752⟩ : DyadicInterval 40),(⟨-206660524096,-206660524032⟩ : DyadicInterval 40),(⟨745902290632,745902309961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32765729344,-32677018688⟩ : DyadicInterval 40),(⟨778461892960,778506267552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨173700206848,173894787520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206660513856,-206385520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e603_ok : ecellOkT e603 = true := by decide +kernel
theorem e603_pos {a z : ℝ} (ha1 : ((350499/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((701847/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e603 e603_ok ha1 ha2 hz1 hz2 hz

-- box ['701847/4096000', '87837/512000', '3999/4000', '1']  interval_lower 7328155/1099511627776
noncomputable def e604 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247263,0,true,173894787456,173894787520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008289,0,false,-206660513856,-206660513792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148966,0,true,174089333632,174089333696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106586,0,false,-206935575744,-206935575680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287865147108,0,true,173854576576,173854576640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911158108444,0,false,-206603675776,-206603675712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535720635,0,true,24092544,24092608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487534917,0,false,-24093184,-24093120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627248,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1287888692349,0,true,173874678080,173874678144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨911134563203,0,false,-206632088576,-206632088512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140157450,0,true,174089340864,174089340928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨910883098102,0,false,-206935585984,-206935585920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067151149443,0,false,-32846245056,-32846244992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067237372952,0,false,-32757410496,-32757410432⟩
    { al := (701847/4096000), au := (87837/512000), zl := (3999/4000), zu := 1,
      A := ⟨188400619487,188628521190⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173854576576,173854576640⟩ : DyadicInterval 40),(⟨-206603675776,-206603675712⟩ : DyadicInterval 40),(⟨745910442042,745910461371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24092859⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24092544,24092608⟩ : DyadicInterval 40),(⟨-24093184,-24093120⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨188377064573,188628529674⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173874678080,173874678144⟩ : DyadicInterval 40),(⟨-206632088576,-206632088512⟩ : DyadicInterval 40),(⟨745906368144,745906387474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089340864,174089340928⟩ : DyadicInterval 40),(⟨-206935585984,-206935585920⟩ : DyadicInterval 40),(⟨745862826419,745862845748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32846245056,-32757410432⟩ : DyadicInterval 40),(⟨778502088832,778546525408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨173894787456,174089333696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206935575744,-206660513792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e604_ok : ecellOkT e604 = true := by decide +kernel
theorem e604_pos {a z : ℝ} (ha1 : ((701847/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87837/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e604 e604_ok ha1 ha2 hz1 hz2 hz

-- box ['87837/512000', '140709/819200', '999/1000', '3997/4000']  interval_lower 5698327/549755813888
noncomputable def e605 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148965,0,true,174089333632,174089333696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106587,0,false,-206935575744,-206935575680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050668,0,true,174283845376,174283845440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204884,0,false,-207210706496,-207210706432⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287951520443,0,true,173928315072,173928315136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911071735109,0,false,-206707908992,-206707908928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288226408351,0,true,174162959168,174162959232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910796847201,0,false,-207039702912,-207039702848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583903738,0,true,72273536,72273600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439351814,0,false,-72278400,-72278336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608118397,0,true,96486336,96486400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415137155,0,false,-96494912,-96494848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619308,0,false,-8512,-8448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623025,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288045830810,0,true,174008824000,174008824064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910977424742,0,false,-206821731776,-206821731712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288297238562,0,true,174223411648,174223411712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910726016990,0,false,-207125212288,-207125212224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067097230384,0,false,-32901800576,-32901800512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067183506076,0,false,-32812907776,-32812907712⟩
    { al := (87837/512000), au := (140709/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨188628521189,188856422892⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173928315072,173928315136⟩ : DyadicInterval 40),(⟨-206707908992,-206707908928⟩ : DyadicInterval 40),(⟨745895494897,745895514227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174162959168,174162959232⟩ : DyadicInterval 40),(⟨-207039702912,-207039702848⟩ : DyadicInterval 40),(⟨745847878229,745847897559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72275962,96490621⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72273536,72273600⟩ : DyadicInterval 40),(⟨-72278400,-72278336⟩ : DyadicInterval 40),(⟨762123381232,762123400562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96486336,96486400⟩ : DyadicInterval 40),(⟨-96494912,-96494848⟩ : DyadicInterval 40),(⟨762123379371,762123398701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8512,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123407136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188534203034,188785610786⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174008824000,174008824064⟩ : DyadicInterval 40),(⟨-206821731776,-206821731712⟩ : DyadicInterval 40),(⟨745879166218,745879185548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174223411648,174223411712⟩ : DyadicInterval 40),(⟨-207125212288,-207125212224⟩ : DyadicInterval 40),(⟨745835597407,745835616736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32901800576,-32812907712⟩ : DyadicInterval 40),(⟨778529837472,778574303168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174089333632,174283845440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207210706496,-206935575680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e605_ok : ecellOkT e605 = true := by decide +kernel
theorem e605_pos {a z : ℝ} (ha1 : ((87837/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((140709/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e605 e605_ok ha1 ha2 hz1 hz2 hz

-- box ['140709/819200', '352197/2048000', '999/1000', '3997/4000']  interval_lower 3489275/274877906944
noncomputable def e606 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050667,0,true,174283845376,174283845440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204885,0,false,-207210706496,-207210706432⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952370,0,true,174478322752,174478322816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303182,0,false,-207485906048,-207485905984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288179194244,0,true,174122660800,174122660864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910844061308,0,false,-206982707648,-206982707584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288454139127,0,true,174357312064,174357312128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910569116425,0,false,-207314653312,-207314653248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583994892,0,true,72364672,72364736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439260660,0,false,-72369536,-72369472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608239957,0,true,96607936,96608000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415015595,0,false,-96616448,-96616384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619286,0,false,-8512,-8448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623013,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288273618557,0,true,174203252736,174203252800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910749636995,0,false,-207096696448,-207096696384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288525054807,0,true,174417826816,174417826880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910498200745,0,false,-207400287296,-207400287232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067018951304,0,false,-32982460480,-32982460416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067105340964,0,false,-32893443712,-32893443648⟩
    { al := (140709/819200), au := (352197/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨188856422891,189084324594⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753448,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174122660800,174122660864⟩ : DyadicInterval 40),(⟨-206982707648,-206982707584⟩ : DyadicInterval 40),(⟨745856061801,745856081131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174357312064,174357312128⟩ : DyadicInterval 40),(⟨-207314653312,-207314653248⟩ : DyadicInterval 40),(⟨745808376587,745808395917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72367116,96612181⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72364672,72364736⟩ : DyadicInterval 40),(⟨-72369536,-72369472⟩ : DyadicInterval 40),(⟨762123381220,762123400550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96607936,96608000⟩ : DyadicInterval 40),(⟨-96616448,-96616384⟩ : DyadicInterval 40),(⟨762123379318,762123398648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8512,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123407136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188761990781,189013427031⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174203252736,174203252800⟩ : DyadicInterval 40),(⟨-207096696448,-207096696384⟩ : DyadicInterval 40),(⟨745839693252,745839712582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174417826816,174417826880⟩ : DyadicInterval 40),(⟨-207400287296,-207400287232⟩ : DyadicInterval 40),(⟨745796065798,745796085127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32982460480,-32893443648⟩ : DyadicInterval 40),(⟨778570105440,778614633120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174283845376,174478322816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207485906048,-207210706432⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e606_ok : ecellOkT e606 = true := by decide +kernel
theorem e606_pos {a z : ℝ} (ha1 : ((140709/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((352197/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e606 e606_ok ha1 ha2 hz1 hz2 hz

-- box ['87837/512000', '140709/819200', '3997/4000', '1999/2000']  interval_lower 5443831/549755813888
noncomputable def e607 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148965,0,true,174089333632,174089333696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106587,0,false,-206935575744,-206935575680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050668,0,true,174283845376,174283845440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204884,0,false,-207210706496,-207210706432⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287998677574,0,true,173968571968,173968572032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911024577978,0,false,-206764821248,-206764821184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288273622457,0,true,174203256064,174203256128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910749633095,0,false,-207096701120,-207096701056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559811929,0,true,48183040,48183104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463443623,0,false,-48185216,-48185152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583996203,0,true,72366016,72366080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439259349,0,false,-72370816,-72370752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623012,0,false,-4800,-4736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625665,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288069408938,0,true,174028950720,174028950784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910953846614,0,false,-206850189952,-206850189888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288320845301,0,true,174243558912,174243558976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910702410251,0,false,-207153712896,-207153712832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067089123346,0,false,-32910153920,-32910153856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067175419647,0,false,-32821239168,-32821239104⟩
    { al := (87837/512000), au := (140709/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨188628521189,188856422892⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173968571968,173968572032⟩ : DyadicInterval 40),(⟨-206764821248,-206764821184⟩ : DyadicInterval 40),(⟨745887331237,745887350567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174203256064,174203256128⟩ : DyadicInterval 40),(⟨-207096701120,-207096701056⟩ : DyadicInterval 40),(⟨745839692561,745839711891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48184153,72368427⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48183040,48183104⟩ : DyadicInterval 40),(⟨-48185216,-48185152⟩ : DyadicInterval 40),(⟨762123382528,762123401857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72366016,72366080⟩ : DyadicInterval 40),(⟨-72370816,-72370752⟩ : DyadicInterval 40),(⟨762123381188,762123400517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188557781162,188809217525⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174028950720,174028950784⟩ : DyadicInterval 40),(⟨-206850189952,-206850189888⟩ : DyadicInterval 40),(⟨745875082678,745875102008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174243558912,174243558976⟩ : DyadicInterval 40),(⟨-207153712896,-207153712832⟩ : DyadicInterval 40),(⟨745831503332,745831522661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32910153920,-32821239104⟩ : DyadicInterval 40),(⟨778534003168,778578479840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174089333632,174283845440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207210706496,-206935575680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e607_ok : ecellOkT e607 = true := by decide +kernel
theorem e607_pos {a z : ℝ} (ha1 : ((87837/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((140709/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e607 e607_ok ha1 ha2 hz1 hz2 hz

-- box ['140709/819200', '352197/2048000', '3997/4000', '1999/2000']  interval_lower 13446431/1099511627776
noncomputable def e608 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050667,0,true,174283845376,174283845440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204885,0,false,-207210706496,-207210706432⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952370,0,true,174478322752,174478322816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303182,0,false,-207485906048,-207485905984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288226408349,0,true,174162959168,174162959232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910796847203,0,false,-207039702912,-207039702848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288501410208,0,true,174397650432,174397650496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910521845344,0,false,-207371734592,-207371734528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559872699,0,true,48243840,48243904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463382853,0,false,-48246016,-48245952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584087375,0,true,72457152,72457216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439168177,0,false,-72462016,-72461952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623000,0,false,-4800,-4736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625660,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288297225167,0,true,174223400256,174223400320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910726030385,0,false,-207125196160,-207125196096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288548690029,0,true,174437994816,174437994880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910474565523,0,false,-207428829376,-207428829312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067010824689,0,false,-32990834560,-32990834496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067097234984,0,false,-32901795840,-32901795776⟩
    { al := (140709/819200), au := (352197/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨188856422891,189084324594⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753448,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174162959168,174162959232⟩ : DyadicInterval 40),(⟨-207039702912,-207039702848⟩ : DyadicInterval 40),(⟨745847878229,745847897559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174397650432,174397650496⟩ : DyadicInterval 40),(⟨-207371734592,-207371734528⟩ : DyadicInterval 40),(⟨745800170973,745800190302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48244923,72459599⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48243840,48243904⟩ : DyadicInterval 40),(⟨-48246016,-48245952⟩ : DyadicInterval 40),(⟨762123382523,762123401852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72457152,72457216⟩ : DyadicInterval 40),(⟨-72462016,-72461952⟩ : DyadicInterval 40),(⟨762123381208,762123400537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188785597391,189037062253⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174223400256,174223400320⟩ : DyadicInterval 40),(⟨-207125196160,-207125196096⟩ : DyadicInterval 40),(⟨745835599724,745835619054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174437994816,174437994880⟩ : DyadicInterval 40),(⟨-207428829376,-207428829312⟩ : DyadicInterval 40),(⟨745791961717,745791981047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32990834560,-32901795776⟩ : DyadicInterval 40),(⟨778574281504,778618820160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174283845376,174478322816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207485906048,-207210706432⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e608_ok : ecellOkT e608 = true := by decide +kernel
theorem e608_pos {a z : ℝ} (ha1 : ((140709/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((352197/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e608 e608_ok ha1 ha2 hz1 hz2 hz

-- box ['352197/2048000', '705243/4096000', '999/1000', '3997/4000']  interval_lower 8265529/549755813888
noncomputable def e609 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952369,0,true,174478322752,174478322816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303183,0,false,-207485906048,-207485905984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854072,0,true,174672765696,174672765760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401480,0,false,-207761174528,-207761174464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288406868044,0,true,174316972224,174316972288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910616387508,0,false,-207257574976,-207257574912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288681869903,0,true,174551630592,174551630656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910341385649,0,false,-207589672448,-207589672384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584086061,0,true,72455872,72455936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439169491,0,false,-72460736,-72460672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608361536,0,true,96729472,96729536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414894016,0,false,-96738048,-96737984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619265,0,false,-8512,-8448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623001,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288501406313,0,true,174397647104,174397647168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910521849239,0,false,-207371729920,-207371729856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288752871048,0,true,174612207552,174612207616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910270384504,0,false,-207675431104,-207675431040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066940577820,0,false,-33063223552,-33063223488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067027081466,0,false,-32974082752,-32974082688⟩
    { al := (352197/2048000), au := (705243/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨189084324593,189312226296⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753449,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174316972224,174316972288⟩ : DyadicInterval 40),(⟨-207257574976,-207257574912⟩ : DyadicInterval 40),(⟨745816580096,745816599425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174551630592,174551630656⟩ : DyadicInterval 40),(⟨-207589672448,-207589672384⟩ : DyadicInterval 40),(⟨745768826339,745768845669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72458285,96733760⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72455872,72455936⟩ : DyadicInterval 40),(⟨-72460736,-72460672⟩ : DyadicInterval 40),(⟨762123381208,762123400538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96729472,96729536⟩ : DyadicInterval 40),(⟨-96738048,-96737984⟩ : DyadicInterval 40),(⟨762123379329,762123398658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8512,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123407136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188989778537,189241243272⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174397647104,174397647168⟩ : DyadicInterval 40),(⟨-207371729920,-207371729856⟩ : DyadicInterval 40),(⟨745800171664,745800190994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174612207552,174612207616⟩ : DyadicInterval 40),(⟨-207675431104,-207675431040⟩ : DyadicInterval 40),(⟨745756485571,745756504901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33063223552,-32974082688⟩ : DyadicInterval 40),(⟨778610424960,778655014656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174478322752,174672765760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207761174528,-207485905984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e609_ok : ecellOkT e609 = true := by decide +kernel
theorem e609_pos {a z : ℝ} (ha1 : ((352197/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((705243/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e609 e609_ok ha1 ha2 hz1 hz2 hz

-- box ['705243/4096000', '176523/1024000', '999/1000', '3997/4000']  interval_lower 19118225/1099511627776
noncomputable def e610 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854071,0,true,174672765696,174672765760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401481,0,false,-207761174528,-207761174464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755774,0,true,174867174272,174867174336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499778,0,false,-208036511936,-208036511872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288634541844,0,true,174511249216,174511249280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910388713708,0,false,-207532511040,-207532510976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288909600679,0,true,174745914752,174745914816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910113654873,0,false,-207864760448,-207864760384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584177243,0,true,72547072,72547136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439078309,0,false,-72551872,-72551808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608483135,0,true,96851072,96851136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414772417,0,false,-96859648,-96859584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619244,0,false,-8576,-8512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622989,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288729194058,0,true,174592007104,174592007168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910294061494,0,false,-207646832128,-207646832064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288980687286,0,true,174806553920,174806553984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910042568266,0,false,-207950643776,-207950643712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066862109931,0,false,-33144089792,-33144089728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066948727590,0,false,-33054825024,-33054824960⟩
    { al := (705243/4096000), au := (176523/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨189312226295,189540127998⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484316,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174511249216,174511249280⟩ : DyadicInterval 40),(⟨-207532511040,-207532510976⟩ : DyadicInterval 40),(⟨745777049873,745777069202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174745914752,174745914816⟩ : DyadicInterval 40),(⟨-207864760448,-207864760384⟩ : DyadicInterval 40),(⟨745729227527,745729246857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72549467,96855359⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72547072,72547136⟩ : DyadicInterval 40),(⟨-72551872,-72551808⟩ : DyadicInterval 40),(⟨762123381164,762123400494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96851072,96851136⟩ : DyadicInterval 40),(⟨-96859648,-96859584⟩ : DyadicInterval 40),(⟨762123379307,762123398637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8576,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123407168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189217566282,189469059510⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174592007104,174592007168⟩ : DyadicInterval 40),(⟨-207646832128,-207646832064⟩ : DyadicInterval 40),(⟨745760601421,745760620751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174806553920,174806553984⟩ : DyadicInterval 40),(⟨-207950643776,-207950643712⟩ : DyadicInterval 40),(⟨745716856704,745716876034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33144089792,-33054824960⟩ : DyadicInterval 40),(⟨778650796096,778695447776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174672765696,174867174336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208036511936,-207761174464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e610_ok : ecellOkT e610 = true := by decide +kernel
theorem e610_pos {a z : ℝ} (ha1 : ((705243/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((176523/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e610 e610_ok ha1 ha2 hz1 hz2 hz

-- box ['352197/2048000', '705243/4096000', '3997/4000', '1999/2000']  interval_lower 8009149/549755813888
noncomputable def e611 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952369,0,true,174478322752,174478322816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303183,0,false,-207485906048,-207485905984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854072,0,true,174672765696,174672765760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401480,0,false,-207761174528,-207761174464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288454139125,0,true,174357312064,174357312128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910569116427,0,false,-207314653312,-207314653248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288729197960,0,true,174592010432,174592010496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910294057592,0,false,-207646836864,-207646836800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559933479,0,true,48304640,48304704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463322073,0,false,-48306816,-48306752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584178560,0,true,72548352,72548416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439076992,0,false,-72553216,-72553152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622988,0,false,-4800,-4736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625654,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288525041407,0,true,174417815360,174417815424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910498214145,0,false,-207400271104,-207400271040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288776534754,0,true,174632396288,174632396352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910246720798,0,false,-207704014784,-207704014720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066932431605,0,false,-33071618432,-33071618368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067018955912,0,false,-32982455680,-32982455616⟩
    { al := (352197/2048000), au := (705243/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨189084324593,189312226296⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753449,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174357312064,174357312128⟩ : DyadicInterval 40),(⟨-207314653312,-207314653248⟩ : DyadicInterval 40),(⟨745808376588,745808395918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174592010432,174592010496⟩ : DyadicInterval 40),(⟨-207646836864,-207646836800⟩ : DyadicInterval 40),(⟨745760600753,745760620082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48305703,72550784⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48304640,48304704⟩ : DyadicInterval 40),(⟨-48306816,-48306752⟩ : DyadicInterval 40),(⟨762123382517,762123401846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72548352,72548416⟩ : DyadicInterval 40),(⟨-72553216,-72553152⟩ : DyadicInterval 40),(⟨762123381196,762123400525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189013413631,189264906978⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174417815360,174417815424⟩ : DyadicInterval 40),(⟨-207400271104,-207400271040⟩ : DyadicInterval 40),(⟨745796068133,745796087462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174632396288,174632396352⟩ : DyadicInterval 40),(⟨-207704014784,-207704014720⟩ : DyadicInterval 40),(⟨745752371512,745752390842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33071618432,-32982455616⟩ : DyadicInterval 40),(⟨778614611424,778659212096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174478322752,174672765760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207761174528,-207485905984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e611_ok : ecellOkT e611 = true := by decide +kernel
theorem e611_pos {a z : ℝ} (ha1 : ((352197/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((705243/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e611 e611_ok ha1 ha2 hz1 hz2 hz

-- box ['705243/4096000', '176523/1024000', '3997/4000', '1999/2000']  interval_lower 18603157/1099511627776
noncomputable def e612 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854071,0,true,174672765696,174672765760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401481,0,false,-207761174528,-207761174464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755774,0,true,174867174272,174867174336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499778,0,false,-208036511936,-208036511872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288681869901,0,true,174551630592,174551630656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910341385651,0,false,-207589672448,-207589672384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288956985711,0,true,174786336128,174786336192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910066269841,0,false,-207922007936,-207922007872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559994269,0,true,48365376,48365440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463261283,0,false,-48367616,-48367552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584269762,0,true,72639552,72639616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438985790,0,false,-72644416,-72644352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622976,0,false,-4864,-4800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625649,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288752857643,0,true,174612196096,174612196160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910270397909,0,false,-207675414912,-207675414848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289004379487,0,true,174826763392,174826763456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910018876065,0,false,-207979269056,-207979268992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066853944088,0,false,-33152505600,-33152505536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066940582435,0,false,-33063218752,-33063218688⟩
    { al := (705243/4096000), au := (176523/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨189312226295,189540127998⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484316,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174551630592,174551630656⟩ : DyadicInterval 40),(⟨-207589672448,-207589672384⟩ : DyadicInterval 40),(⟨745768826340,745768845669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174786336128,174786336192⟩ : DyadicInterval 40),(⟨-207922007936,-207922007872⟩ : DyadicInterval 40),(⟨745720981854,745721001184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48366493,72641986⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48365376,48365440⟩ : DyadicInterval 40),(⟨-48367616,-48367552⟩ : DyadicInterval 40),(⟨762123382544,762123401873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72639552,72639616⟩ : DyadicInterval 40),(⟨-72644416,-72644352⟩ : DyadicInterval 40),(⟨762123381184,762123400513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189241229867,189492751711⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174612196096,174612196160⟩ : DyadicInterval 40),(⟨-207675414912,-207675414848⟩ : DyadicInterval 40),(⟨745756487913,745756507242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174826763392,174826763456⟩ : DyadicInterval 40),(⟨-207979269056,-207979268992⟩ : DyadicInterval 40),(⟨745712732640,745712751970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33152505600,-33063218688⟩ : DyadicInterval 40),(⟨778654992960,778699655680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174672765696,174867174336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208036511936,-207761174464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e612_ok : ecellOkT e612 = true := by decide +kernel
theorem e612_pos {a z : ℝ} (ha1 : ((705243/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((176523/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e612 e612_ok ha1 ha2 hz1 hz2 hz

-- box ['87837/512000', '140709/819200', '1999/2000', '3999/4000']  interval_lower 2594675/274877906944
noncomputable def e613 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148965,0,true,174089333632,174089333696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106587,0,false,-206935575744,-206935575680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050668,0,true,174283845376,174283845440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204884,0,false,-207210706496,-207210706432⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288045834704,0,true,174008827328,174008827392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910977420848,0,false,-206821736512,-206821736448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288320836563,0,true,174243551488,174243551552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910702418989,0,false,-207153702336,-207153702272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535719856,0,true,24091776,24091840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487535696,0,false,-24092352,-24092288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559873745,0,true,48244864,48244928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463381807,0,false,-48247040,-48246976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625658,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627249,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288092987183,0,true,174049077248,174049077312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910930268369,0,false,-206878649024,-206878648960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288344452163,0,true,174263705920,174263705984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910678803389,0,false,-207182214336,-207182214272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067081015252,0,false,-32918508416,-32918508352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067167332166,0,false,-32829571776,-32829571712⟩
    { al := (87837/512000), au := (140709/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨188628521189,188856422892⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174008827328,174008827392⟩ : DyadicInterval 40),(⟨-206821736512,-206821736448⟩ : DyadicInterval 40),(⟨745879165557,745879184886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174243551488,174243551552⟩ : DyadicInterval 40),(⟨-207153702336,-207153702272⟩ : DyadicInterval 40),(⟨745831504824,745831524153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24092080,48245969⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24091776,24091840⟩ : DyadicInterval 40),(⟨-24092352,-24092288⟩ : DyadicInterval 40),(⟨762123383312,762123402641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48244864,48244928⟩ : DyadicInterval 40),(⟨-48247040,-48246976⟩ : DyadicInterval 40),(⟨762123382522,762123401852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188581359407,188832824387⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174049077248,174049077312⟩ : DyadicInterval 40),(⟨-206878649024,-206878648960⟩ : DyadicInterval 40),(⟨745870998560,745871017890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174263705920,174263705984⟩ : DyadicInterval 40),(⟨-207182214336,-207182214272⟩ : DyadicInterval 40),(⟨745827408686,745827428016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32918508416,-32829571712⟩ : DyadicInterval 40),(⟨778538169472,778582657088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174089333632,174283845440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207210706496,-206935575680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e613_ok : ecellOkT e613 = true := by decide +kernel
theorem e613_pos {a z : ℝ} (ha1 : ((87837/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((140709/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e613 e613_ok ha1 ha2 hz1 hz2 hz

-- box ['140709/819200', '352197/2048000', '1999/2000', '3999/4000']  interval_lower 6467607/549755813888
noncomputable def e614 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050667,0,true,174283845376,174283845440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204885,0,false,-207210706496,-207210706432⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952370,0,true,174478322752,174478322816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303182,0,false,-207485906048,-207485905984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288273622455,0,true,174203256064,174203256128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910749633097,0,false,-207096701120,-207096701056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288548681290,0,true,174437987328,174437987392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910474574262,0,false,-207428818816,-207428818752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535750241,0,true,24122176,24122240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487505311,0,false,-24122752,-24122688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559934527,0,true,48305664,48305728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463321025,0,false,-48307840,-48307776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625653,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627247,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288320831905,0,true,174243547520,174243547584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910702423647,0,false,-207153696704,-207153696640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288572325380,0,true,174458162496,174458162560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910450930172,0,false,-207457372416,-207457372352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067002697014,0,false,-32999209856,-32999209792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067089127947,0,false,-32910149184,-32910149120⟩
    { al := (140709/819200), au := (352197/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨188856422891,189084324594⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753448,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174203256064,174203256128⟩ : DyadicInterval 40),(⟨-207096701120,-207096701056⟩ : DyadicInterval 40),(⟨745839692562,745839711891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174437987328,174437987392⟩ : DyadicInterval 40),(⟨-207428818816,-207428818752⟩ : DyadicInterval 40),(⟨745791963251,745791982580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24122465,48306751⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24122176,24122240⟩ : DyadicInterval 40),(⟨-24122752,-24122688⟩ : DyadicInterval 40),(⟨762123383310,762123402639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48305664,48305728⟩ : DyadicInterval 40),(⟨-48307840,-48307776⟩ : DyadicInterval 40),(⟨762123382517,762123401846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188809204129,189060697604⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174243547520,174243547584⟩ : DyadicInterval 40),(⟨-207153696704,-207153696640⟩ : DyadicInterval 40),(⟨745831505624,745831524953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174458162496,174458162560⟩ : DyadicInterval 40),(⟨-207457372416,-207457372352⟩ : DyadicInterval 40),(⟨745787857153,745787876482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32999209856,-32910149120⟩ : DyadicInterval 40),(⟨778578458176,778623007808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174283845376,174478322816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207485906048,-207210706432⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e614_ok : ecellOkT e614 = true := by decide +kernel
theorem e614_pos {a z : ℝ} (ha1 : ((140709/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((352197/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e614 e614_ok ha1 ha2 hz1 hz2 hz

-- box ['87837/512000', '140709/819200', '3999/4000', '1']  interval_lower 1233645/137438953472
noncomputable def e615 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148965,0,true,174089333632,174089333696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106587,0,false,-206935575744,-206935575680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050668,0,true,174283845376,174283845440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204884,0,false,-207210706496,-207210706432⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288092991834,0,true,174049081216,174049081280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910930263718,0,false,-206878654656,-206878654592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535751021,0,true,24122944,24123008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487504531,0,false,-24123520,-24123456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627246,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1288116565558,0,true,174069203456,174069203520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨910906689994,0,false,-206907108992,-206907108928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368059147,0,true,174283852608,174283852672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨910655196405,0,false,-207210716736,-207210716672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067072906102,0,false,-32926864064,-32926864000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067159243630,0,false,-32837905472,-32837905408⟩
    { al := (87837/512000), au := (140709/819200), zl := (3999/4000), zu := 1,
      A := ⟨188628521189,188856422892⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174049081216,174049081280⟩ : DyadicInterval 40),(⟨-206878654656,-206878654592⟩ : DyadicInterval 40),(⟨745870997763,745871017093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24123245⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24122944,24123008⟩ : DyadicInterval 40),(⟨-24123520,-24123456⟩ : DyadicInterval 40),(⟨762123383310,762123402639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨188604937782,188856431371⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174069203456,174069203520⟩ : DyadicInterval 40),(⟨-206907108992,-206907108928⟩ : DyadicInterval 40),(⟨745866913936,745866933266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283852608,174283852672⟩ : DyadicInterval 40),(⟨-207210716736,-207210716672⟩ : DyadicInterval 40),(⟨745823313559,745823332889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32926864064,-32837905408⟩ : DyadicInterval 40),(⟨778542336320,778586834912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨174089333632,174283845440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207210706496,-206935575680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e615_ok : ecellOkT e615 = true := by decide +kernel
theorem e615_pos {a z : ℝ} (ha1 : ((87837/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((140709/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e615 e615_ok ha1 ha2 hz1 hz2 hz

-- box ['140709/819200', '352197/2048000', '3999/4000', '1']  interval_lower 12423557/1099511627776
noncomputable def e616 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288368050667,0,true,174283845376,174283845440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910655204885,0,false,-207210706496,-207210706432⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952370,0,true,174478322752,174478322816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303182,0,false,-207485906048,-207485905984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288320836561,0,true,174243551488,174243551552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910702418991,0,false,-207153702336,-207153702272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535781413,0,true,24153344,24153408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487474139,0,false,-24153920,-24153856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627245,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1288344438767,0,true,174263694464,174263694528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨910678816785,0,false,-207182198208,-207182198144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595960856,0,true,174478329984,174478330048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨910427294696,0,false,-207485916288,-207485916224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066994568280,0,false,-33007586304,-33007586240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067081019854,0,false,-32918503680,-32918503616⟩
    { al := (140709/819200), au := (352197/2048000), zl := (3999/4000), zu := 1,
      A := ⟨188856422891,189084324594⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174283845376,174283845440⟩ : DyadicInterval 40),(⟨-207210706496,-207210706432⟩ : DyadicInterval 40),(⟨745823315027,745823334357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753448,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174243551488,174243551552⟩ : DyadicInterval 40),(⟨-207153702336,-207153702272⟩ : DyadicInterval 40),(⟨745831504824,745831524153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753448,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24153637⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24153344,24153408⟩ : DyadicInterval 40),(⟨-24153920,-24153856⟩ : DyadicInterval 40),(⟨762123383309,762123402638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨188832810991,189084333080⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174263694464,174263694528⟩ : DyadicInterval 40),(⟨-207182198208,-207182198144⟩ : DyadicInterval 40),(⟨745827411042,745827430372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478329984,174478330048⟩ : DyadicInterval 40),(⟨-207485916288,-207485916224⟩ : DyadicInterval 40),(⟨745783751976,745783771306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33007586304,-32918503616⟩ : DyadicInterval 40),(⟨778582635424,778627196032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨174283845376,174478322816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207485906048,-207210706432⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e616_ok : ecellOkT e616 = true := by decide +kernel
theorem e616_pos {a z : ℝ} (ha1 : ((140709/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((352197/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e616 e616_ok ha1 ha2 hz1 hz2 hz

-- box ['352197/2048000', '705243/4096000', '1999/2000', '3999/4000']  interval_lower 15505001/1099511627776
noncomputable def e617 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952369,0,true,174478322752,174478322816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303183,0,false,-207485906048,-207485905984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854072,0,true,174672765696,174672765760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401480,0,false,-207761174528,-207761174464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288501410206,0,true,174397650432,174397650496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910521845346,0,false,-207371734592,-207371734528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288776526016,0,true,174632388800,174632388864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910246729536,0,false,-207704004224,-207704004160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535780632,0,true,24152576,24152640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487474920,0,false,-24153152,-24153088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559995319,0,true,48366464,48366528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463260233,0,false,-48368640,-48368576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625648,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627246,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288548676628,0,true,174437983360,174437983424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910474578924,0,false,-207428813184,-207428813120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288800198590,0,true,174652584768,174652584832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910223056962,0,false,-207732599296,-207732599232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066924284326,0,false,-33080014528,-33080014464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067010829298,0,false,-32990829824,-32990829760⟩
    { al := (352197/2048000), au := (705243/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨189084324593,189312226296⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753449,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174397650432,174397650496⟩ : DyadicInterval 40),(⟨-207371734592,-207371734528⟩ : DyadicInterval 40),(⟨745800170973,745800190302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174632388800,174632388864⟩ : DyadicInterval 40),(⟨-207704004224,-207704004160⟩ : DyadicInterval 40),(⟨745752373049,745752392379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24152856,48367543⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24152576,24152640⟩ : DyadicInterval 40),(⟨-24153152,-24153088⟩ : DyadicInterval 40),(⟨762123383309,762123402638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48366464,48366528⟩ : DyadicInterval 40),(⟨-48368640,-48368576⟩ : DyadicInterval 40),(⟨762123382512,762123401841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189037048852,189288570814⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174437983360,174437983424⟩ : DyadicInterval 40),(⟨-207428813184,-207428813120⟩ : DyadicInterval 40),(⟨745791964054,745791983383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174652584768,174652584832⟩ : DyadicInterval 40),(⟨-207732599296,-207732599232⟩ : DyadicInterval 40),(⟨745748256876,745748276205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33080014528,-32990829760⟩ : DyadicInterval 40),(⟨778618798496,778663410144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174478322752,174672765760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207761174528,-207485905984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e617_ok : ecellOkT e617 = true := by decide +kernel
theorem e617_pos {a z : ℝ} (ha1 : ((352197/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((705243/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e617 e617_ok ha1 ha2 hz1 hz2 hz

-- box ['705243/4096000', '176523/1024000', '1999/2000', '3999/4000']  interval_lower 4521937/274877906944
noncomputable def e618 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854071,0,true,174672765696,174672765760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401481,0,false,-207761174528,-207761174464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755774,0,true,174867174272,174867174336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499778,0,false,-208036511936,-208036511872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288729197957,0,true,174592010432,174592010496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910294057595,0,false,-207646836864,-207646836800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289004370743,0,true,174826755968,174826756032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910018884809,0,false,-207979258432,-207979258368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535811027,0,true,24182976,24183040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487444525,0,false,-24183552,-24183488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560056120,0,true,48427264,48427328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463199432,0,false,-48429440,-48429376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625642,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627245,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288776521348,0,true,174632384832,174632384896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910246734204,0,false,-207703998592,-207703998528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289028071811,0,true,174846972608,174846972672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909995183741,0,false,-208007895168,-208007895104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066845777181,0,false,-33160922560,-33160922496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066932436221,0,false,-33071613696,-33071613632⟩
    { al := (705243/4096000), au := (176523/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨189312226295,189540127998⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484316,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174592010432,174592010496⟩ : DyadicInterval 40),(⟨-207646836864,-207646836800⟩ : DyadicInterval 40),(⟨745760600753,745760620083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174826755968,174826756032⟩ : DyadicInterval 40),(⟨-207979258432,-207979258368⟩ : DyadicInterval 40),(⟨745712734118,745712753447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24183251,48428344⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24182976,24183040⟩ : DyadicInterval 40),(⟨-24183552,-24183488⟩ : DyadicInterval 40),(⟨762123383308,762123402637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48427264,48427328⟩ : DyadicInterval 40),(⟨-48429440,-48429376⟩ : DyadicInterval 40),(⟨762123382506,762123401836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189264893572,189516444035⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174632384832,174632384896⟩ : DyadicInterval 40),(⟨-207703998592,-207703998528⟩ : DyadicInterval 40),(⟨745752373855,745752393184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174846972608,174846972672⟩ : DyadicInterval 40),(⟨-208007895168,-208007895104⟩ : DyadicInterval 40),(⟨745708607996,745708627326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33160922560,-33071613632⟩ : DyadicInterval 40),(⟨778659190432,778703864160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174672765696,174867174336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208036511936,-207761174464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e618_ok : ecellOkT e618 = true := by decide +kernel
theorem e618_pos {a z : ℝ} (ha1 : ((705243/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((176523/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e618 e618_ok ha1 ha2 hz1 hz2 hz

-- box ['352197/2048000', '705243/4096000', '3999/4000', '1']  interval_lower 7495719/549755813888
noncomputable def e619 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288595952369,0,true,174478322752,174478322816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910427303183,0,false,-207485906048,-207485905984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854072,0,true,174672765696,174672765760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401480,0,false,-207761174528,-207761174464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288548681287,0,true,174437987328,174437987392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910474574265,0,false,-207428818816,-207428818752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535811809,0,true,24183744,24183808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487443743,0,false,-24184320,-24184256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627244,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1288572311979,0,true,174458151104,174458151168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨910450943573,0,false,-207457356224,-207457356160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823862555,0,true,174672772928,174672772992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨910199392997,0,false,-207761184768,-207761184704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066916135985,0,false,-33088411776,-33088411712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067002701624,0,false,-32999205120,-32999205056⟩
    { al := (352197/2048000), au := (705243/4096000), zl := (3999/4000), zu := 1,
      A := ⟨189084324593,189312226296⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174478322752,174478322816⟩ : DyadicInterval 40),(⟨-207485906048,-207485905984⟩ : DyadicInterval 40),(⟨745783753449,745783772778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174437987328,174437987392⟩ : DyadicInterval 40),(⟨-207428818816,-207428818752⟩ : DyadicInterval 40),(⟨745791963251,745791982581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24184033⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24183744,24183808⟩ : DyadicInterval 40),(⟨-24184320,-24184256⟩ : DyadicInterval 40),(⟨762123383308,762123402637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨189060684203,189312234779⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174458151104,174458151168⟩ : DyadicInterval 40),(⟨-207457356224,-207457356160⟩ : DyadicInterval 40),(⟨745787859452,745787878781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672772928,174672772992⟩ : DyadicInterval 40),(⟨-207761184768,-207761184704⟩ : DyadicInterval 40),(⟨745744141752,745744161082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33088411776,-32999205056⟩ : DyadicInterval 40),(⟨778622986144,778667608768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨174478322752,174672765760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-207761174528,-207485905984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e619_ok : ecellOkT e619 = true := by decide +kernel
theorem e619_pos {a z : ℝ} (ha1 : ((352197/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((705243/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e619 e619_ok ha1 ha2 hz1 hz2 hz

-- box ['705243/4096000', '176523/1024000', '3999/4000', '1']  interval_lower 17572257/1099511627776
noncomputable def e620 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1288823854071,0,true,174672765696,174672765760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨910199401481,0,false,-207761174528,-207761174464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755774,0,true,174867174272,174867174336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499778,0,false,-208036511936,-208036511872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288776526014,0,true,174632388800,174632388864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910246729538,0,false,-207704004224,-207704004160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535842211,0,true,24214144,24214208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487413341,0,false,-24214720,-24214656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627242,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1288800185183,0,true,174652573312,174652573376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨910223070369,0,false,-207732583104,-207732583040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051764257,0,true,174867181504,174867181568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨909971491295,0,false,-208036522176,-208036522112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066837609212,0,false,-33169340608,-33169340544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066924288943,0,false,-33080009792,-33080009728⟩
    { al := (705243/4096000), au := (176523/1024000), zl := (3999/4000), zu := 1,
      A := ⟨189312226295,189540127998⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174672765696,174672765760⟩ : DyadicInterval 40),(⟨-207761174528,-207761174464⟩ : DyadicInterval 40),(⟨745744143228,745744162558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484316,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174632388800,174632388864⟩ : DyadicInterval 40),(⟨-207704004224,-207704004160⟩ : DyadicInterval 40),(⟨745752373049,745752392379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484316,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24214435⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24214144,24214208⟩ : DyadicInterval 40),(⟨-24214720,-24214656⟩ : DyadicInterval 40),(⟨762123383306,762123402635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨189288557407,189540136481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174652573312,174652573376⟩ : DyadicInterval 40),(⟨-207732583104,-207732583040⟩ : DyadicInterval 40),(⟨745748259219,745748278549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867181504,174867181568⟩ : DyadicInterval 40),(⟨-208036522176,-208036522112⟩ : DyadicInterval 40),(⟨745704482838,745704502167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33169340608,-33080009728⟩ : DyadicInterval 40),(⟨778663388480,778708073184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨174672765696,174867174336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208036511936,-207761174464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e620_ok : ecellOkT e620 = true := by decide +kernel
theorem e620_pos {a z : ℝ} (ha1 : ((705243/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((176523/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e620 e620_ok ha1 ha2 hz1 hz2 hz

-- box ['176523/1024000', '706941/4096000', '999/1000', '3997/4000']  interval_lower 21718813/1099511627776
noncomputable def e621 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755773,0,true,174867174272,174867174336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499779,0,false,-208036511936,-208036511872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657477,0,true,175061548480,175061548544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598075,0,false,-208311918336,-208311918272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288862215644,0,true,174705491968,174705492032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910161039908,0,false,-207807515904,-207807515840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289137331455,0,true,174940164608,174940164672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909885924097,0,false,-208139917248,-208139917184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584268441,0,true,72638208,72638272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438987111,0,false,-72643072,-72643008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608604752,0,true,96972672,96972736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414650800,0,false,-96981312,-96981248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619222,0,false,-8576,-8512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622977,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288956981808,0,true,174786332800,174786332864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910066273744,0,false,-207922003264,-207922003200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289208503525,0,true,175000865984,175000866048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909814752027,0,false,-208225925376,-208225925312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066783547635,0,false,-33225059392,-33225059328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066870279329,0,false,-33135670464,-33135670400⟩
    { al := (176523/1024000), au := (706941/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨189540127997,189768029701⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484317,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174705491968,174705492032⟩ : DyadicInterval 40),(⟨-207807515904,-207807515840⟩ : DyadicInterval 40),(⟨745737471035,745737490364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174940164608,174940164672⟩ : DyadicInterval 40),(⟨-208139917248,-208139917184⟩ : DyadicInterval 40),(⟨745689580075,745689599405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72640665,96976976⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72638208,72638272⟩ : DyadicInterval 40),(⟨-72643072,-72643008⟩ : DyadicInterval 40),(⟨762123381184,762123400514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96972672,96972736⟩ : DyadicInterval 40),(⟨-96981312,-96981248⟩ : DyadicInterval 40),(⟨762123379318,762123398648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8576,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123407168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189445354032,189696875749⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174786332800,174786332864⟩ : DyadicInterval 40),(⟨-207922003264,-207922003200⟩ : DyadicInterval 40),(⟨745720982551,745721001880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175000865984,175000866048⟩ : DyadicInterval 40),(⟨-208225925376,-208225925312⟩ : DyadicInterval 40),(⟨745677179175,745677198504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33225059392,-33135670400⟩ : DyadicInterval 40),(⟨778691218816,778735932576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174867174272,175061548544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208311918336,-208036511872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e621_ok : ecellOkT e621 = true := by decide +kernel
theorem e621_pos {a z : ℝ} (ha1 : ((176523/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((706941/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e621 e621_ok ha1 ha2 hz1 hz2 hz

-- box ['706941/4096000', '70779/409600', '999/1000', '3997/4000']  interval_lower 6083133/274877906944
noncomputable def e622 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657476,0,true,175061548480,175061548544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598076,0,false,-208311918336,-208311918272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559179,0,true,175255888384,175255888448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696373,0,false,-208587393728,-208587393664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289089889446,0,true,174899700352,174899700416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909933366106,0,false,-208082589504,-208082589440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289365062231,0,true,175134380224,175134380288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909658193321,0,false,-208415142912,-208415142848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584359653,0,true,72729408,72729472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438895899,0,false,-72734336,-72734272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608726389,0,true,97094272,97094336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414529163,0,false,-97102912,-97102848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619201,0,false,-8576,-8512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622965,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289184769558,0,true,174980624064,174980624128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909838485994,0,false,-208197243200,-208197243136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289436319775,0,true,175195143680,175195143744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909586935777,0,false,-208501275904,-208501275840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066704890930,0,false,-33306132160,-33306132096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066791736686,0,false,-33216619136,-33216619072⟩
    { al := (706941/4096000), au := (70779/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨189768029700,189995931403⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174899700352,174899700416⟩ : DyadicInterval 40),(⟨-208082589504,-208082589440⟩ : DyadicInterval 40),(⟨745697843619,745697862949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175134380224,175134380288⟩ : DyadicInterval 40),(⟨-208415142912,-208415142848⟩ : DyadicInterval 40),(⟨745649883963,745649903293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72731877,97098613⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72729408,72729472⟩ : DyadicInterval 40),(⟨-72734336,-72734272⟩ : DyadicInterval 40),(⟨762123381204,762123400534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97094272,97094336⟩ : DyadicInterval 40),(⟨-97102912,-97102848⟩ : DyadicInterval 40),(⟨762123379296,762123398626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8576,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123407168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189673141782,189924691999⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174980624064,174980624128⟩ : DyadicInterval 40),(⟨-208197243200,-208197243136⟩ : DyadicInterval 40),(⟨745681315066,745681334395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175195143680,175195143744⟩ : DyadicInterval 40),(⟨-208501275904,-208501275840⟩ : DyadicInterval 40),(⟨745637453008,745637472337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33306132160,-33216619072⟩ : DyadicInterval 40),(⟨778731693152,778776468960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175061548480,175255888448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208587393728,-208311918272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e622_ok : ecellOkT e622 = true := by decide +kernel
theorem e622_pos {a z : ℝ} (ha1 : ((706941/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((70779/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e622 e622_ok ha1 ha2 hz1 hz2 hz

-- box ['176523/1024000', '706941/4096000', '3997/4000', '1999/2000']  interval_lower 10600763/549755813888
noncomputable def e623 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755773,0,true,174867174272,174867174336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499779,0,false,-208036511936,-208036511872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657477,0,true,175061548480,175061548544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598075,0,false,-208311918336,-208311918272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288909600676,0,true,174745914752,174745914816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910113654876,0,false,-207864760448,-207864760384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289184773463,0,true,174980627392,174980627456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909838482089,0,false,-208197247936,-208197247872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560055068,0,true,48426176,48426240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463200484,0,false,-48428416,-48428352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584360977,0,true,72730752,72730816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438894575,0,false,-72735616,-72735552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622964,0,false,-4864,-4800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625644,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1288980673874,0,true,174806542464,174806542528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910042581678,0,false,-207950627584,-207950627520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289232224209,0,true,175021096192,175021096256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909791031343,0,false,-208254592192,-208254592128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066775362145,0,false,-33233496000,-33233495936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066862114554,0,false,-33144085056,-33144084992⟩
    { al := (176523/1024000), au := (706941/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨189540127997,189768029701⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484317,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174745914752,174745914816⟩ : DyadicInterval 40),(⟨-207864760448,-207864760384⟩ : DyadicInterval 40),(⟨745729227527,745729246857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174980627392,174980627456⟩ : DyadicInterval 40),(⟨-208197247936,-208197247872⟩ : DyadicInterval 40),(⟨745681314393,745681333723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48427292,72733201⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48426176,48426240⟩ : DyadicInterval 40),(⟨-48428416,-48428352⟩ : DyadicInterval 40),(⟨762123382539,762123401868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72730752,72730816⟩ : DyadicInterval 40),(⟨-72735616,-72735552⟩ : DyadicInterval 40),(⟨762123381172,762123400501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189469046098,189720596433⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174806542464,174806542528⟩ : DyadicInterval 40),(⟨-207950627584,-207950627520⟩ : DyadicInterval 40),(⟨745716859053,745716878382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175021096192,175021096256⟩ : DyadicInterval 40),(⟨-208254592192,-208254592128⟩ : DyadicInterval 40),(⟨745673045055,745673064384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33233496000,-33144084992⟩ : DyadicInterval 40),(⟨778695426112,778740150880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174867174272,175061548544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208311918336,-208036511872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e623_ok : ecellOkT e623 = true := by decide +kernel
theorem e623_pos {a z : ℝ} (ha1 : ((176523/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((706941/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e623 e623_ok ha1 ha2 hz1 hz2 hz

-- box ['706941/4096000', '70779/409600', '3997/4000', '1999/2000']  interval_lower 5953293/274877906944
noncomputable def e624 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657476,0,true,175061548480,175061548544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598076,0,false,-208311918336,-208311918272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559179,0,true,175255888384,175255888448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696373,0,false,-208587393728,-208587393664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289137331453,0,true,174940164608,174940164672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909885924099,0,false,-208139917248,-208139917184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289412561214,0,true,175174884416,175174884480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909610694338,0,false,-208472556864,-208472556800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560115877,0,true,48486976,48487040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463139675,0,false,-48489216,-48489152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584452205,0,true,72822016,72822080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438803347,0,false,-72826880,-72826816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622952,0,false,-4864,-4800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625638,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289208490109,0,true,175000854528,175000854592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909814765443,0,false,-208225909184,-208225909120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289460068941,0,true,175215394560,175215394624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909563186611,0,false,-208529984320,-208529984256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066696685769,0,false,-33314589696,-33314589632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066783552266,0,false,-33225054592,-33225054528⟩
    { al := (706941/4096000), au := (70779/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨189768029700,189995931403⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174940164608,174940164672⟩ : DyadicInterval 40),(⟨-208139917248,-208139917184⟩ : DyadicInterval 40),(⟨745689580076,745689599406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175174884416,175174884480⟩ : DyadicInterval 40),(⟨-208472556864,-208472556800⟩ : DyadicInterval 40),(⟨745641598248,745641617577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48488101,72824429⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48486976,48487040⟩ : DyadicInterval 40),(⟨-48489216,-48489152⟩ : DyadicInterval 40),(⟨762123382533,762123401862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72822016,72822080⟩ : DyadicInterval 40),(⟨-72826880,-72826816⟩ : DyadicInterval 40),(⟨762123381160,762123400489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189696862333,189948441165⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175000854528,175000854592⟩ : DyadicInterval 40),(⟨-208225909184,-208225909120⟩ : DyadicInterval 40),(⟨745677181530,745677200859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175215394560,175215394624⟩ : DyadicInterval 40),(⟨-208529984320,-208529984256⟩ : DyadicInterval 40),(⟨745633308871,745633328201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33314589696,-33225054528⟩ : DyadicInterval 40),(⟨778735910880,778780697728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175061548480,175255888448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208587393728,-208311918272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e624_ok : ecellOkT e624 = true := by decide +kernel
theorem e624_pos {a z : ℝ} (ha1 : ((706941/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((70779/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e624 e624_ok ha1 ha2 hz1 hz2 hz

-- box ['70779/409600', '708639/4096000', '999/1000', '3997/4000']  interval_lower 26959601/1099511627776
noncomputable def e625 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559178,0,true,175255888384,175255888448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696374,0,false,-208587393728,-208587393664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460881,0,true,175450193856,175450193920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794671,0,false,-208862938112,-208862938048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289317563246,0,true,175093874496,175093874560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909705692306,0,false,-208357732032,-208357731968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289592793007,0,true,175328561472,175328561536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909430462545,0,false,-208690437504,-208690437440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584450880,0,true,72820672,72820736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438804672,0,false,-72825536,-72825472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608848046,0,true,97215936,97216000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414407506,0,false,-97224576,-97224512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619179,0,false,-8640,-8576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622953,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289412557309,0,true,175174881088,175174881152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909610698243,0,false,-208472552128,-208472552064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289664136014,0,true,175389387072,175389387136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909359119538,0,false,-208776695424,-208776695360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066626139823,0,false,-33387308288,-33387308224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066713099660,0,false,-33297671040,-33297670976⟩
    { al := (70779/409600), au := (708639/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨189995931402,190223833105⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175093874496,175093874560⟩ : DyadicInterval 40),(⟨-208357732032,-208357731968⟩ : DyadicInterval 40),(⟨745658167620,745658186950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175328561472,175328561536⟩ : DyadicInterval 40),(⟨-208690437504,-208690437440⟩ : DyadicInterval 40),(⟨745610139281,745610158611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72823104,97220270⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72820672,72820736⟩ : DyadicInterval 40),(⟨-72825536,-72825472⟩ : DyadicInterval 40),(⟨762123381160,762123400489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97215936,97216000⟩ : DyadicInterval 40),(⟨-97224576,-97224512⟩ : DyadicInterval 40),(⟨762123379275,762123398605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8640,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123407200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189900929533,190152508238⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175174881088,175174881152⟩ : DyadicInterval 40),(⟨-208472552128,-208472552064⟩ : DyadicInterval 40),(⟨745641598921,745641618251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175389387072,175389387136⟩ : DyadicInterval 40),(⟨-208776695424,-208776695360⟩ : DyadicInterval 40),(⟨745597678185,745597697515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33387308288,-33297670976⟩ : DyadicInterval 40),(⟨778772219104,778817057024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175255888384,175450193920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208862938112,-208587393664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e625_ok : ecellOkT e625 = true := by decide +kernel
theorem e625_pos {a z : ℝ} (ha1 : ((70779/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((708639/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e625 e625_ok ha1 ha2 hz1 hz2 hz

-- box ['708639/4096000', '44343/256000', '999/1000', '3997/4000']  interval_lower 29600137/1099511627776
noncomputable def e626 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460880,0,true,175450193856,175450193920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794672,0,false,-208862938112,-208862938048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362583,0,true,175644465088,175644465152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892969,0,false,-209138551616,-209138551552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289545237046,0,true,175288014336,175288014400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909478018506,0,false,-208632943360,-208632943296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289820523783,0,true,175522708416,175522708480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909202731769,0,false,-208965801088,-208965801024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584542120,0,true,72911872,72911936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438713432,0,false,-72916800,-72916736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099608969722,0,true,97337600,97337664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414285830,0,false,-97346304,-97346240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619158,0,false,-8640,-8576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622941,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289640345059,0,true,175369103744,175369103808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909382910493,0,false,-208747929984,-208747929920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289891952254,0,true,175583596160,175583596224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909131303298,0,false,-209052183936,-209052183872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066547294309,0,false,-33468587712,-33468587648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066634368253,0,false,-33378826176,-33378826112⟩
    { al := (708639/4096000), au := (44343/256000), zl := (999/1000), zu := (3997/4000),
      A := ⟨190223833104,190451734807⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175288014336,175288014400⟩ : DyadicInterval 40),(⟨-208632943360,-208632943296⟩ : DyadicInterval 40),(⟨745618443013,745618462342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175522708416,175522708480⟩ : DyadicInterval 40),(⟨-208965801088,-208965801024⟩ : DyadicInterval 40),(⟨745570346007,745570365337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72914344,97341946⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72911872,72911936⟩ : DyadicInterval 40),(⟨-72916800,-72916736⟩ : DyadicInterval 40),(⟨762123381180,762123400509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97337600,97337664⟩ : DyadicInterval 40),(⟨-97346304,-97346240⟩ : DyadicInterval 40),(⟨762123379285,762123398615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8640,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123407200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190128717283,190380324478⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175369103744,175369103808⟩ : DyadicInterval 40),(⟨-208747929984,-208747929920⟩ : DyadicInterval 40),(⟨745601834156,745601853486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175583596160,175583596224⟩ : DyadicInterval 40),(⟨-209052183936,-209052183872⟩ : DyadicInterval 40),(⟨745557854695,745557874025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33468587712,-33378826112⟩ : DyadicInterval 40),(⟨778812796672,778857696736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175450193856,175644465152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209138551616,-208862938048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e626_ok : ecellOkT e626 = true := by decide +kernel
theorem e626_pos {a z : ℝ} (ha1 : ((708639/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((44343/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e626 e626_ok ha1 ha2 hz1 hz2 hz

-- box ['70779/409600', '708639/4096000', '3997/4000', '1999/2000']  interval_lower 26438521/1099511627776
noncomputable def e627 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559178,0,true,175255888384,175255888448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696374,0,false,-208587393728,-208587393664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460881,0,true,175450193856,175450193920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794671,0,false,-208862938112,-208862938048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289365062229,0,true,175134380160,175134380224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909658193323,0,false,-208415142912,-208415142848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289640348965,0,true,175369107072,175369107136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909382906587,0,false,-208747934720,-208747934656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560176695,0,true,48547840,48547904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463078857,0,false,-48550016,-48549952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584543449,0,true,72913216,72913280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438712103,0,false,-72918144,-72918080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622940,0,false,-4864,-4800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625633,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289436306348,0,true,175195132224,175195132288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909586949204,0,false,-208501259648,-208501259584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289687913666,0,true,175409658688,175409658752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909335341886,0,false,-208805445504,-208805445440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066617914966,0,false,-33395786752,-33395786688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066704895570,0,false,-33306127424,-33306127360⟩
    { al := (70779/409600), au := (708639/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨189995931402,190223833105⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175134380160,175134380224⟩ : DyadicInterval 40),(⟨-208415142912,-208415142848⟩ : DyadicInterval 40),(⟨745649884001,745649903331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175369107072,175369107136⟩ : DyadicInterval 40),(⟨-208747934720,-208747934656⟩ : DyadicInterval 40),(⟨745601833481,745601852811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48548919,72915673⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48547840,48547904⟩ : DyadicInterval 40),(⟨-48550016,-48549952⟩ : DyadicInterval 40),(⟨762123382496,762123401825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72913216,72913280⟩ : DyadicInterval 40),(⟨-72918144,-72918080⟩ : DyadicInterval 40),(⟨762123381180,762123400509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189924678572,190176285890⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175195132224,175195132288⟩ : DyadicInterval 40),(⟨-208501259648,-208501259584⟩ : DyadicInterval 40),(⟨745637455344,745637474674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175409658688,175409658752⟩ : DyadicInterval 40),(⟨-208805445504,-208805445440⟩ : DyadicInterval 40),(⟨745593523995,745593543325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33395786752,-33306127360⟩ : DyadicInterval 40),(⟨778776447296,778821296256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175255888384,175450193920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208862938112,-208587393664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e627_ok : ecellOkT e627 = true := by decide +kernel
theorem e627_pos {a z : ℝ} (ha1 : ((70779/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((708639/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e627 e627_ok ha1 ha2 hz1 hz2 hz

-- box ['708639/4096000', '44343/256000', '3997/4000', '1999/2000']  interval_lower 7269191/274877906944
noncomputable def e628 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460880,0,true,175450193856,175450193920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794672,0,false,-208862938112,-208862938048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362583,0,true,175644465088,175644465152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892969,0,false,-209138551616,-209138551552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289592793005,0,true,175328561472,175328561536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909430462547,0,false,-208690437504,-208690437440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289868136716,0,true,175563295488,175563295552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909155118836,0,false,-209023381568,-209023381504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560237524,0,true,48608640,48608704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463018028,0,false,-48610880,-48610816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584634707,0,true,73004480,73004544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438620845,0,false,-73009408,-73009344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622928,0,false,-4864,-4800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625627,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289664122587,0,true,175389375616,175389375680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909359132965,0,false,-208776679168,-208776679104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289915758399,0,true,175603888448,175603888512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909107497153,0,false,-209080975680,-209080975616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066539049730,0,false,-33477087168,-33477087104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066626144468,0,false,-33387303488,-33387303424⟩
    { al := (708639/4096000), au := (44343/256000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨190223833104,190451734807⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175328561472,175328561536⟩ : DyadicInterval 40),(⟨-208690437504,-208690437440⟩ : DyadicInterval 40),(⟨745610139281,745610158611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175563295488,175563295552⟩ : DyadicInterval 40),(⟨-209023381568,-209023381504⟩ : DyadicInterval 40),(⟨745562020034,745562039364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48609748,73006931⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48608640,48608704⟩ : DyadicInterval 40),(⟨-48610880,-48610816⟩ : DyadicInterval 40),(⟨762123382522,762123401851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73004480,73004544⟩ : DyadicInterval 40),(⟨-73009408,-73009344⟩ : DyadicInterval 40),(⟨762123381168,762123400497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190152494811,190404130623⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175389375616,175389375680⟩ : DyadicInterval 40),(⟨-208776679168,-208776679104⟩ : DyadicInterval 40),(⟨745597680527,745597699857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175603888448,175603888512⟩ : DyadicInterval 40),(⟨-209080975680,-209080975616⟩ : DyadicInterval 40),(⟨745553690461,745553709791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33477087168,-33387303424⟩ : DyadicInterval 40),(⟨778817035328,778861946464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175450193856,175644465152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209138551616,-208862938048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e628_ok : ecellOkT e628 = true := by decide +kernel
theorem e628_pos {a z : ℝ} (ha1 : ((708639/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((44343/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e628 e628_ok ha1 ha2 hz1 hz2 hz

-- box ['176523/1024000', '706941/4096000', '1999/2000', '3999/4000']  interval_lower 20684023/1099511627776
noncomputable def e629 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755773,0,true,174867174272,174867174336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499779,0,false,-208036511936,-208036511872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657477,0,true,175061548480,175061548544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598075,0,false,-208311918336,-208311918272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1288956985708,0,true,174786336064,174786336128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910066269844,0,false,-207922007936,-207922007872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289232215470,0,true,175021088704,175021088768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909791040082,0,false,-208254581632,-208254581568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535841427,0,true,24213376,24213440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487414125,0,false,-24213952,-24213888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560116931,0,true,48488064,48488128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463138621,0,false,-48490240,-48490176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625637,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627243,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289004366069,0,true,174826751936,174826752000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨910018889483,0,false,-207979252800,-207979252736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289255945022,0,true,175041326080,175041326144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909767310530,0,false,-208283259968,-208283259904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066767175586,0,false,-33241933824,-33241933760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066853948714,0,false,-33152500800,-33152500736⟩
    { al := (176523/1024000), au := (706941/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨189540127997,189768029701⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484317,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174786336064,174786336128⟩ : DyadicInterval 40),(⟨-207922007936,-207922007872⟩ : DyadicInterval 40),(⟨745720981892,745721001222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175021088704,175021088768⟩ : DyadicInterval 40),(⟨-208254581632,-208254581568⟩ : DyadicInterval 40),(⟨745673046599,745673065929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24213651,48489155⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24213376,24213440⟩ : DyadicInterval 40),(⟨-24213952,-24213888⟩ : DyadicInterval 40),(⟨762123383306,762123402635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48488064,48488128⟩ : DyadicInterval 40),(⟨-48490240,-48490176⟩ : DyadicInterval 40),(⟨762123382501,762123401830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189492738293,189744317246⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174826751936,174826752000⟩ : DyadicInterval 40),(⟨-207979252800,-207979252736⟩ : DyadicInterval 40),(⟨745712734964,745712754293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175041326080,175041326144⟩ : DyadicInterval 40),(⟨-208283259968,-208283259904⟩ : DyadicInterval 40),(⟨745668910443,745668929772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33241933824,-33152500736⟩ : DyadicInterval 40),(⟨778699633984,778744369792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨174867174272,175061548544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208311918336,-208036511872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e629_ok : ecellOkT e629 = true := by decide +kernel
theorem e629_pos {a z : ℝ} (ha1 : ((176523/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((706941/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e629 e629_ok ha1 ha2 hz1 hz2 hz

-- box ['706941/4096000', '70779/409600', '1999/2000', '3999/4000']  interval_lower 11646925/549755813888
noncomputable def e630 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657476,0,true,175061548480,175061548544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598076,0,false,-208311918336,-208311918272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559179,0,true,175255888384,175255888448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696373,0,false,-208587393728,-208587393664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289184773461,0,true,174980627392,174980627456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909838482091,0,false,-208197247936,-208197247872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289460060197,0,true,175215387136,175215387200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909563195355,0,false,-208529973760,-208529973696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535871832,0,true,24243776,24243840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487383720,0,false,-24244352,-24244288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560177751,0,true,48548864,48548928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463077801,0,false,-48551104,-48551040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625632,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627242,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289232210792,0,true,175021084736,175021084800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909791044760,0,false,-208254576000,-208254575936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289483818240,0,true,175235645248,175235645312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909539437312,0,false,-208558693696,-208558693632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066688479536,0,false,-33323048448,-33323048384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066775366776,0,false,-33233491264,-33233491200⟩
    { al := (706941/4096000), au := (70779/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨189768029700,189995931403⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174980627392,174980627456⟩ : DyadicInterval 40),(⟨-208197247936,-208197247872⟩ : DyadicInterval 40),(⟨745681314393,745681333723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175215387136,175215387200⟩ : DyadicInterval 40),(⟨-208529973760,-208529973696⟩ : DyadicInterval 40),(⟨745633310383,745633329712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24244056,48549975⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24243776,24243840⟩ : DyadicInterval 40),(⟨-24244352,-24244288⟩ : DyadicInterval 40),(⟨762123383305,762123402634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48548864,48548928⟩ : DyadicInterval 40),(⟨-48551104,-48551040⟩ : DyadicInterval 40),(⟨762123382528,762123401857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189720583016,189972190464⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175021084736,175021084800⟩ : DyadicInterval 40),(⟨-208254576000,-208254575936⟩ : DyadicInterval 40),(⟨745673047411,745673066740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175235645248,175235645312⟩ : DyadicInterval 40),(⟨-208558693696,-208558693632⟩ : DyadicInterval 40),(⟨745629164164,745629183493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33323048448,-33233491200⟩ : DyadicInterval 40),(⟨778740129216,778784927104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175061548480,175255888448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208587393728,-208311918272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e630_ok : ecellOkT e630 = true := by decide +kernel
theorem e630_pos {a z : ℝ} (ha1 : ((706941/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((70779/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e630 e630_ok ha1 ha2 hz1 hz2 hz

-- box ['176523/1024000', '706941/4096000', '3999/4000', '1']  interval_lower 1260395/68719476736
noncomputable def e631 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289051755773,0,true,174867174272,174867174336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909971499779,0,false,-208036511936,-208036511872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657477,0,true,175061548480,175061548544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598075,0,false,-208311918336,-208311918272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289004370740,0,true,174826755968,174826756032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨910018884812,0,false,-207979258432,-207979258368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535872616,0,true,24244544,24244608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487382936,0,false,-24245120,-24245056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627241,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1289028058398,0,true,174846961152,174846961216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨909995197154,0,false,-208007878976,-208007878912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279665957,0,true,175061555712,175061555776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨909743589595,0,false,-208311928576,-208311928512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066758987962,0,false,-33250372800,-33250372736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066845781806,0,false,-33160917760,-33160917696⟩
    { al := (176523/1024000), au := (706941/4096000), zl := (3999/4000), zu := 1,
      A := ⟨189540127997,189768029701⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174867174272,174867174336⟩ : DyadicInterval 40),(⟨-208036511936,-208036511872⟩ : DyadicInterval 40),(⟨745704484317,745704503646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174826755968,174826756032⟩ : DyadicInterval 40),(⟨-207979258432,-207979258368⟩ : DyadicInterval 40),(⟨745712734118,745712753447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24244840⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24244544,24244608⟩ : DyadicInterval 40),(⟨-24245120,-24245056⟩ : DyadicInterval 40),(⟨762123383305,762123402634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨189516430622,189768038181⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174846961152,174846961216⟩ : DyadicInterval 40),(⟨-208007878976,-208007878912⟩ : DyadicInterval 40),(⟨745708610346,745708629676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061555712,175061555776⟩ : DyadicInterval 40),(⟨-208311928576,-208311928512⟩ : DyadicInterval 40),(⟨745664775248,745664794578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33250372800,-33160917696⟩ : DyadicInterval 40),(⟨778703842464,778748589280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨174867174272,175061548544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208311918336,-208036511872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e631_ok : ecellOkT e631 = true := by decide +kernel
theorem e631_pos {a z : ℝ} (ha1 : ((176523/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((706941/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e631 e631_ok ha1 ha2 hz1 hz2 hz

-- box ['706941/4096000', '70779/409600', '3999/4000', '1']  interval_lower 5693413/274877906944
noncomputable def e632 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289279657476,0,true,175061548480,175061548544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909743598076,0,false,-208311918336,-208311918272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559179,0,true,175255888384,175255888448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696373,0,false,-208587393728,-208587393664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289232215468,0,true,175021088704,175021088768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909791040084,0,false,-208254581632,-208254581568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535903028,0,true,24274944,24275008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487352524,0,false,-24275520,-24275456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627240,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1289255931604,0,true,175041314624,175041314688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨909767323948,0,false,-208283243712,-208283243648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507567665,0,true,175255895616,175255895680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨909515687887,0,false,-208587403968,-208587403904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066680272233,0,false,-33331508352,-33331508288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066767180218,0,false,-33241929024,-33241928960⟩
    { al := (706941/4096000), au := (70779/409600), zl := (3999/4000), zu := 1,
      A := ⟨189768029700,189995931403⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175061548480,175061548544⟩ : DyadicInterval 40),(⟨-208311918336,-208311918272⟩ : DyadicInterval 40),(⟨745664776730,745664796060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175021088704,175021088768⟩ : DyadicInterval 40),(⟨-208254581632,-208254581568⟩ : DyadicInterval 40),(⟨745673046600,745673065929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24275252⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24274944,24275008⟩ : DyadicInterval 40),(⟨-24275520,-24275456⟩ : DyadicInterval 40),(⟨762123383304,762123402633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨189744303828,189995939889⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175041314624,175041314688⟩ : DyadicInterval 40),(⟨-208283243712,-208283243648⟩ : DyadicInterval 40),(⟨745668912773,745668932102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255895616,175255895680⟩ : DyadicInterval 40),(⟨-208587403968,-208587403904⟩ : DyadicInterval 40),(⟨745625018935,745625038264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33331508352,-33241928960⟩ : DyadicInterval 40),(⟨778744348096,778789157056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨175061548480,175255888448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208587393728,-208311918272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e632_ok : ecellOkT e632 = true := by decide +kernel
theorem e632_pos {a z : ℝ} (ha1 : ((706941/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((70779/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e632 e632_ok ha1 ha2 hz1 hz2 hz

-- box ['70779/409600', '708639/4096000', '1999/2000', '3999/4000']  interval_lower 25916679/1099511627776
noncomputable def e633 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559178,0,true,175255888384,175255888448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696374,0,false,-208587393728,-208587393664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460881,0,true,175450193856,175450193920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794671,0,false,-208862938112,-208862938048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289412561212,0,true,175174884416,175174884480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909610694340,0,false,-208472556864,-208472556800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289687904923,0,true,175409651264,175409651328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909335350629,0,false,-208805434944,-208805434880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535902242,0,true,24274176,24274240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487353310,0,false,-24274752,-24274688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560238581,0,true,48609728,48609792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463016971,0,false,-48611904,-48611840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625626,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627241,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289460055519,0,true,175215383168,175215383232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909563200033,0,false,-208529968128,-208529968064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289711691452,0,true,175429930048,175429930112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909311564100,0,false,-208834196480,-208834196416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066609689034,0,false,-33404266432,-33404266368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066696690407,0,false,-33314584960,-33314584896⟩
    { al := (70779/409600), au := (708639/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨189995931402,190223833105⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175174884416,175174884480⟩ : DyadicInterval 40),(⟨-208472556864,-208472556800⟩ : DyadicInterval 40),(⟨745641598248,745641617577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175409651264,175409651328⟩ : DyadicInterval 40),(⟨-208805434944,-208805434880⟩ : DyadicInterval 40),(⟨745593525510,745593544840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24274466,48610805⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24274176,24274240⟩ : DyadicInterval 40),(⟨-24274752,-24274688⟩ : DyadicInterval 40),(⟨762123383304,762123402633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48609728,48609792⟩ : DyadicInterval 40),(⟨-48611904,-48611840⟩ : DyadicInterval 40),(⟨762123382490,762123401819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨189948427743,190200063676⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175215383168,175215383232⟩ : DyadicInterval 40),(⟨-208529968128,-208529968064⟩ : DyadicInterval 40),(⟨745633311196,745633330526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175429930048,175429930112⟩ : DyadicInterval 40),(⟨-208834196480,-208834196416⟩ : DyadicInterval 40),(⟨745589369241,745589388571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33404266432,-33314584896⟩ : DyadicInterval 40),(⟨778780676064,778825536096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175255888384,175450193920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208862938112,-208587393664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e633_ok : ecellOkT e633 = true := by decide +kernel
theorem e633_pos {a z : ℝ} (ha1 : ((70779/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((708639/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e633 e633_ok ha1 ha2 hz1 hz2 hz

-- box ['708639/4096000', '44343/256000', '1999/2000', '3999/4000']  interval_lower 28552907/1099511627776
noncomputable def e634 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460880,0,true,175450193856,175450193920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794672,0,false,-208862938112,-208862938048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362583,0,true,175644465088,175644465152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892969,0,false,-209138551616,-209138551552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289640348963,0,true,175369107072,175369107136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909382906589,0,false,-208747934720,-208747934656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1289915749650,0,true,175603881024,175603881088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨909107505902,0,false,-209080965056,-209080964992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535932657,0,true,24304576,24304640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487322895,0,false,-24305152,-24305088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560299421,0,true,48670528,48670592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462956131,0,false,-48672768,-48672704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625621,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627239,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289687900238,0,true,175409647232,175409647296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909335355314,0,false,-208805429248,-208805429184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1289939564671,0,true,175624180544,175624180608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨909083690881,0,false,-209109768320,-209109768256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066530804077,0,false,-33485587776,-33485587712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066617919612,0,false,-33395781952,-33395781888⟩
    { al := (708639/4096000), au := (44343/256000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨190223833104,190451734807⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175369107072,175369107136⟩ : DyadicInterval 40),(⟨-208747934720,-208747934656⟩ : DyadicInterval 40),(⟨745601833481,745601852811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175603881024,175603881088⟩ : DyadicInterval 40),(⟨-209080965056,-209080964992⟩ : DyadicInterval 40),(⟨745553691954,745553711284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24304881,48671645⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24304576,24304640⟩ : DyadicInterval 40),(⟨-24305152,-24305088⟩ : DyadicInterval 40),(⟨762123383302,762123402631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48670528,48670592⟩ : DyadicInterval 40),(⟨-48672768,-48672704⟩ : DyadicInterval 40),(⟨762123382517,762123401846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190176272462,190427936895⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175409647232,175409647296⟩ : DyadicInterval 40),(⟨-208805429248,-208805429184⟩ : DyadicInterval 40),(⟨745593526338,745593545668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175624180544,175624180608⟩ : DyadicInterval 40),(⟨-209109768320,-209109768256⟩ : DyadicInterval 40),(⟨745549525626,745549544955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33485587776,-33395781888⟩ : DyadicInterval 40),(⟨778821274560,778866196768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175450193856,175644465152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209138551616,-208862938048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e634_ok : ecellOkT e634 = true := by decide +kernel
theorem e634_pos {a z : ℝ} (ha1 : ((708639/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((44343/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e634 e634_ok ha1 ha2 hz1 hz2 hz

-- box ['70779/409600', '708639/4096000', '3999/4000', '1']  interval_lower 3174341/137438953472
noncomputable def e635 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289507559178,0,true,175255888384,175255888448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909515696374,0,false,-208587393728,-208587393664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460881,0,true,175450193856,175450193920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794671,0,false,-208862938112,-208862938048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289460060195,0,true,175215387136,175215387200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909563195357,0,false,-208529973760,-208529973696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535933443,0,true,24305344,24305408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487322109,0,false,-24305984,-24305920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627238,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1289483804816,0,true,175235633792,175235633856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨909539450736,0,false,-208558677504,-208558677440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735469364,0,true,175450201088,175450201152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨909287786188,0,false,-208862948352,-208862948288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066601462031,0,false,-33412747200,-33412747136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066688484176,0,false,-33323043648,-33323043584⟩
    { al := (70779/409600), au := (708639/4096000), zl := (3999/4000), zu := 1,
      A := ⟨189995931402,190223833105⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175255888384,175255888448⟩ : DyadicInterval 40),(⟨-208587393728,-208587393664⟩ : DyadicInterval 40),(⟨745625020422,745625039751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175215387136,175215387200⟩ : DyadicInterval 40),(⟨-208529973760,-208529973696⟩ : DyadicInterval 40),(⟨745633310383,745633329712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24305667⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24305344,24305408⟩ : DyadicInterval 40),(⟨-24305984,-24305920⟩ : DyadicInterval 40),(⟨762123383334,762123402663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨189972177040,190223841588⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175235633792,175235633856⟩ : DyadicInterval 40),(⟨-208558677504,-208558677440⟩ : DyadicInterval 40),(⟨745629166527,745629185857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450201088,175450201152⟩ : DyadicInterval 40),(⟨-208862948352,-208862948288⟩ : DyadicInterval 40),(⟨745585213964,745585233293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33412747200,-33323043584⟩ : DyadicInterval 40),(⟨778784905408,778829776480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨175255888384,175450193920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-208862938112,-208587393664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e635_ok : ecellOkT e635 = true := by decide +kernel
theorem e635_pos {a z : ℝ} (ha1 : ((70779/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((708639/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e635 e635_ok ha1 ha2 hz1 hz2 hz

-- box ['708639/4096000', '44343/256000', '3999/4000', '1']  interval_lower 14014397/549755813888
noncomputable def e636 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289735460880,0,true,175450193856,175450193920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909287794672,0,false,-208862938112,-208862938048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362583,0,true,175644465088,175644465152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892969,0,false,-209138551616,-209138551552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289687904921,0,true,175409651200,175409651264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909335350631,0,false,-208805434880,-208805434816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535963863,0,true,24335808,24335872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487291689,0,false,-24336384,-24336320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627237,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1289711678023,0,true,175429918592,175429918656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨909311577529,0,false,-208834180224,-208834180160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963371072,0,true,175644472320,175644472384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨909059884480,0,false,-209138561856,-209138561792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066522557348,0,false,-33494089536,-33494089472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066609693681,0,false,-33404261632,-33404261568⟩
    { al := (708639/4096000), au := (44343/256000), zl := (3999/4000), zu := 1,
      A := ⟨190223833104,190451734807⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175450193856,175450193920⟩ : DyadicInterval 40),(⟨-208862938112,-208862938048⟩ : DyadicInterval 40),(⟨745585215454,745585234783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175409651200,175409651264⟩ : DyadicInterval 40),(⟨-208805434880,-208805434816⟩ : DyadicInterval 40),(⟨745593525521,745593544851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24336087⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24335808,24335872⟩ : DyadicInterval 40),(⟨-24336384,-24336320⟩ : DyadicInterval 40),(⟨762123383301,762123402630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨190200050247,190451743296⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175429918592,175429918656⟩ : DyadicInterval 40),(⟨-208834180224,-208834180160⟩ : DyadicInterval 40),(⟨745589371585,745589390915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644472320,175644472384⟩ : DyadicInterval 40),(⟨-209138561856,-209138561792⟩ : DyadicInterval 40),(⟨745545360263,745545379592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33494089536,-33404261568⟩ : DyadicInterval 40),(⟨778825514400,778870447648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨175450193856,175644465152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209138551616,-208862938048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e636_ok : ecellOkT e636 = true := by decide +kernel
theorem e636_pos {a z : ℝ} (ha1 : ((708639/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((44343/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e636 e636_ok ha1 ha2 hz1 hz2 hz

-- box ['44343/256000', '710337/4096000', '999/1000', '3997/4000']  interval_lower 16127077/549755813888
noncomputable def e637 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362582,0,true,175644465088,175644465152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892970,0,false,-209138551616,-209138551552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264285,0,true,175838701952,175838702016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991267,0,false,-209414234176,-209414234112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289772910847,0,true,175482119872,175482119936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909250344705,0,false,-208908223552,-208908223488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290048254558,0,true,175716821120,175716821184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908975000994,0,false,-209241233600,-209241233536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584633375,0,true,73003136,73003200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438622177,0,false,-73008064,-73008000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609091417,0,true,97459264,97459328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414164135,0,false,-97467968,-97467904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619136,0,false,-8704,-8640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622929,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289868132812,0,true,175563292160,175563292224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909155122740,0,false,-209023376832,-209023376768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290119768498,0,true,175777770944,175777771008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908903487054,0,false,-209327741440,-209327741376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066468354388,0,false,-33549970496,-33549970432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066555542462,0,false,-33460084672,-33460084608⟩
    { al := (44343/256000), au := (710337/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨190451734806,190679636509⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175482119872,175482119936⟩ : DyadicInterval 40),(⟨-208908223552,-208908223488⟩ : DyadicInterval 40),(⟨745578669810,745578689140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175716821120,175716821184⟩ : DyadicInterval 40),(⟨-209241233600,-209241233536⟩ : DyadicInterval 40),(⟨745530504067,745530523396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73005599,97463641⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73003136,73003200⟩ : DyadicInterval 40),(⟨-73008064,-73008000⟩ : DyadicInterval 40),(⟨762123381168,762123400497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97459264,97459328⟩ : DyadicInterval 40),(⟨-97467968,-97467904⟩ : DyadicInterval 40),(⟨762123379264,762123398593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8704,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123407232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190356505036,190608140722⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175563292160,175563292224⟩ : DyadicInterval 40),(⟨-209023376832,-209023376768⟩ : DyadicInterval 40),(⟨745562020711,745562040040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175777770944,175777771008⟩ : DyadicInterval 40),(⟨-209327741440,-209327741376⟩ : DyadicInterval 40),(⟨745517982525,745518001854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33549970496,-33460084608⟩ : DyadicInterval 40),(⟨778853425920,778898388128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175644465088,175838702016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209414234176,-209138551552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e637_ok : ecellOkT e637 = true := by decide +kernel
theorem e637_pos {a z : ℝ} (ha1 : ((44343/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((710337/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e637 e637_ok ha1 ha2 hz1 hz2 hz

-- box ['710337/4096000', '355593/2048000', '999/1000', '3997/4000']  interval_lower 34921487/1099511627776
noncomputable def e638 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264284,0,true,175838701952,175838702016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991268,0,false,-209414234176,-209414234112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165987,0,true,176032904512,176032904576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089565,0,false,-209689985920,-209689985856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290000584647,0,true,175676191168,175676191232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909022670905,0,false,-209183572736,-209183572672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290275985334,0,true,175910899520,175910899584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908747270218,0,false,-209516735104,-209516735040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584724645,0,true,73094400,73094464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438530907,0,false,-73099328,-73099264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609213131,0,true,97580992,97581056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099414042421,0,false,-97589696,-97589632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619114,0,false,-8704,-8640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622917,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290095920564,0,true,175757446208,175757446272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908927334988,0,false,-209298892736,-209298892672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290347584739,0,true,175971911424,175971911488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908675670813,0,false,-209603368064,-209603368000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066389320062,0,false,-33631456640,-33631456576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066476622289,0,false,-33541446464,-33541446400⟩
    { al := (710337/4096000), au := (355593/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨190679636508,190907538211⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175676191168,175676191232⟩ : DyadicInterval 40),(⟨-209183572736,-209183572672⟩ : DyadicInterval 40),(⟨745538848019,745538867349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175910899520,175910899584⟩ : DyadicInterval 40),(⟨-209516735104,-209516735040⟩ : DyadicInterval 40),(⟨745490613513,745490632842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73096869,97585355⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73094400,73094464⟩ : DyadicInterval 40),(⟨-73099328,-73099264⟩ : DyadicInterval 40),(⟨762123381156,762123400485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97580992,97581056⟩ : DyadicInterval 40),(⟨-97589696,-97589632⟩ : DyadicInterval 40),(⟨762123379242,762123398572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8704,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123407232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190584292788,190835956963⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175757446208,175757446272⟩ : DyadicInterval 40),(⟨-209298892736,-209298892672⟩ : DyadicInterval 40),(⟨745522158676,745522178006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175971911424,175971911488⟩ : DyadicInterval 40),(⟨-209603368064,-209603368000⟩ : DyadicInterval 40),(⟨745478061718,745478081048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33631456640,-33541446400⟩ : DyadicInterval 40),(⟨778894106816,778939131200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175838701952,176032904576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209689985920,-209414234112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e638_ok : ecellOkT e638 = true := by decide +kernel
theorem e638_pos {a z : ℝ} (ha1 : ((710337/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((355593/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e638 e638_ok ha1 ha2 hz1 hz2 hz

-- box ['44343/256000', '710337/4096000', '3997/4000', '1999/2000']  interval_lower 15864335/549755813888
noncomputable def e639 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362582,0,true,175644465088,175644465152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892970,0,false,-209138551616,-209138551552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264285,0,true,175838701952,175838702016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991267,0,false,-209414234176,-209414234112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289820523780,0,true,175522708416,175522708480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909202731772,0,false,-208965801088,-208965801024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290095924467,0,true,175757449536,175757449600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908927331085,0,false,-209298897408,-209298897344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560298361,0,true,48669504,48669568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462957191,0,false,-48671680,-48671616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584725980,0,true,73095744,73095808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438529572,0,false,-73100672,-73100608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622916,0,false,-4864,-4800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625622,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289891938822,0,true,175583584704,175583584768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909131316730,0,false,-209052167680,-209052167616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290143603127,0,true,175798083968,175798084032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908879652425,0,false,-209356574912,-209356574848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066460090067,0,false,-33558490880,-33558490816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066547298961,0,false,-33468582912,-33468582848⟩
    { al := (44343/256000), au := (710337/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨190451734806,190679636509⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175522708416,175522708480⟩ : DyadicInterval 40),(⟨-208965801088,-208965801024⟩ : DyadicInterval 40),(⟨745570346008,745570365337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175757449536,175757449600⟩ : DyadicInterval 40),(⟨-209298897408,-209298897344⟩ : DyadicInterval 40),(⟨745522157971,745522177301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48670585,73098204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48669504,48669568⟩ : DyadicInterval 40),(⟨-48671680,-48671616⟩ : DyadicInterval 40),(⟨762123382485,762123401814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73095744,73095808⟩ : DyadicInterval 40),(⟨-73100672,-73100608⟩ : DyadicInterval 40),(⟨762123381156,762123400485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190380311046,190631975351⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175583584704,175583584768⟩ : DyadicInterval 40),(⟨-209052167680,-209052167616⟩ : DyadicInterval 40),(⟨745557857043,745557876373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175798083968,175798084032⟩ : DyadicInterval 40),(⟨-209356574912,-209356574848⟩ : DyadicInterval 40),(⟨745513808213,745513827542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33558490880,-33468582848⟩ : DyadicInterval 40),(⟨778857675040,778902648320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175644465088,175838702016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209414234176,-209138551552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e639_ok : ecellOkT e639 = true := by decide +kernel
theorem e639_pos {a z : ℝ} (ha1 : ((44343/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((710337/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e639 e639_ok ha1 ha2 hz1 hz2 hz

-- box ['710337/4096000', '355593/2048000', '3997/4000', '1999/2000']  interval_lower 8598499/274877906944
noncomputable def e640 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264284,0,true,175838701952,175838702016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991268,0,false,-209414234176,-209414234112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165987,0,true,176032904512,176032904576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089565,0,false,-209689985920,-209689985856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290048254556,0,true,175716821120,175716821184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908975000996,0,false,-209241233600,-209241233536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290323712219,0,true,175951569344,175951569408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908699543333,0,false,-209574482368,-209574482304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560359210,0,true,48730304,48730368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462896342,0,false,-48732544,-48732480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584817267,0,true,73187008,73187072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438438285,0,false,-73191936,-73191872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622904,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625617,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290119755060,0,true,175777759488,175777759552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908903500492,0,false,-209327725184,-209327725120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290371447853,0,true,175992245120,175992245184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908651807699,0,false,-209632243200,-209632243136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066381035975,0,false,-33639998080,-33639998016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066468359048,0,false,-33549965696,-33549965632⟩
    { al := (710337/4096000), au := (355593/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨190679636508,190907538211⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175716821120,175716821184⟩ : DyadicInterval 40),(⟨-209241233600,-209241233536⟩ : DyadicInterval 40),(⟨745530504067,745530523397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175951569344,175951569408⟩ : DyadicInterval 40),(⟨-209574482368,-209574482304⟩ : DyadicInterval 40),(⟨745482247259,745482266589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48731434,73189491⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48730304,48730368⟩ : DyadicInterval 40),(⟨-48732544,-48732480⟩ : DyadicInterval 40),(⟨762123382512,762123401841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73187008,73187072⟩ : DyadicInterval 40),(⟨-73191936,-73191872⟩ : DyadicInterval 40),(⟨762123381143,762123400473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190608127284,190859820077⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175777759488,175777759552⟩ : DyadicInterval 40),(⟨-209327725184,-209327725120⟩ : DyadicInterval 40),(⟨745517984880,745518004209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175992245120,175992245184⟩ : DyadicInterval 40),(⟨-209632243200,-209632243136⟩ : DyadicInterval 40),(⟨745473877313,745473896643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33639998080,-33549965632⟩ : DyadicInterval 40),(⟨778898366432,778943401920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175838701952,176032904576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209689985920,-209414234112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e640_ok : ecellOkT e640 = true := by decide +kernel
theorem e640_pos {a z : ℝ} (ha1 : ((710337/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((355593/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e640 e640_ok ha1 ha2 hz1 hz2 hz

-- box ['355593/2048000', '142407/819200', '999/1000', '3997/4000']  interval_lower 18801335/549755813888
noncomputable def e641 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165986,0,true,176032904512,176032904576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089566,0,false,-209689985920,-209689985856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067689,0,true,176227072768,176227072832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187863,0,false,-209965806848,-209965806784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290228258447,0,true,175870228224,175870228288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908794997105,0,false,-209458990912,-209458990848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290503716110,0,true,176104943744,176104943808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908519539442,0,false,-209792305728,-209792305664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584815929,0,true,73185664,73185728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438439623,0,false,-73190592,-73190528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609334864,0,true,97702720,97702784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413920688,0,false,-97711488,-97711424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619093,0,false,-8704,-8640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622905,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290323708312,0,true,175951566016,175951566080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908699547240,0,false,-209574477632,-209574477568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290575400980,0,true,176166017664,176166017728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908447854572,0,false,-209879063808,-209879063744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066310191330,0,false,-33713046144,-33713046080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066397607735,0,false,-33622911552,-33622911488⟩
    { al := (355593/2048000), au := (142407/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨190907538210,191135439913⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175870228224,175870228288⟩ : DyadicInterval 40),(⟨-209458990912,-209458990848⟩ : DyadicInterval 40),(⟨745498977628,745498996957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176104943744,176104943808⟩ : DyadicInterval 40),(⟨-209792305728,-209792305664⟩ : DyadicInterval 40),(⟨745450674313,745450693642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73188153,97707088⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73185664,73185728⟩ : DyadicInterval 40),(⟨-73190592,-73190528⟩ : DyadicInterval 40),(⟨762123381144,762123400473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97702720,97702784⟩ : DyadicInterval 40),(⟨-97711488,-97711424⟩ : DyadicInterval 40),(⟨762123379252,762123398582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8704,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123407232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190812080536,191063773204⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175951566016,175951566080⟩ : DyadicInterval 40),(⟨-209574477632,-209574477568⟩ : DyadicInterval 40),(⟨745482247940,745482267269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176166017664,176166017728⟩ : DyadicInterval 40),(⟨-209879063808,-209879063744⟩ : DyadicInterval 40),(⟨745438092226,745438111555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33713046144,-33622911488⟩ : DyadicInterval 40),(⟨778934839360,778979925952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176032904512,176227072832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209965806848,-209689985856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e641_ok : ecellOkT e641 = true := by decide +kernel
theorem e641_pos {a z : ℝ} (ha1 : ((355593/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((142407/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e641 e641_ok ha1 ha2 hz1 hz2 hz

-- box ['142407/819200', '178221/1024000', '999/1000', '3997/4000']  interval_lower 40297237/1099511627776
noncomputable def e642 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067688,0,true,176227072768,176227072832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187864,0,false,-209965806848,-209965806784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969392,0,true,176421206720,176421206784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286160,0,false,-210241696960,-210241696896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290455932248,0,true,176064231040,176064231104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908567323304,0,false,-209734478080,-209734478016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290731446886,0,true,176298953664,176298953728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908291808666,0,false,-210067945344,-210067945280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584907228,0,true,73276992,73277056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438348324,0,false,-73281920,-73281856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609456617,0,true,97824448,97824512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413798935,0,false,-97833216,-97833152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619071,0,false,-8768,-8704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622893,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290551496061,0,true,176145651584,176145651648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908471759491,0,false,-209850131648,-209850131584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290803217221,0,true,176360089600,176360089664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908220038331,0,false,-210154828736,-210154828672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066230968192,0,false,-33794739072,-33794739008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066318498798,0,false,-33704480064,-33704480000⟩
    { al := (142407/819200), au := (178221/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨191135439912,191363341616⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176064231040,176064231104⟩ : DyadicInterval 40),(⟨-209734478080,-209734478016⟩ : DyadicInterval 40),(⟨745459058626,745459077956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176298953664,176298953728⟩ : DyadicInterval 40),(⟨-210067945344,-210067945280⟩ : DyadicInterval 40),(⟨745410686478,745410705807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73279452,97828841⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73276992,73277056⟩ : DyadicInterval 40),(⟨-73281920,-73281856⟩ : DyadicInterval 40),(⟨762123381131,762123400461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97824448,97824512⟩ : DyadicInterval 40),(⟨-97833216,-97833152⟩ : DyadicInterval 40),(⟨762123379231,762123398561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8768,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123407264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191039868285,191291589445⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176145651584,176145651648⟩ : DyadicInterval 40),(⟨-209850131648,-209850131584⟩ : DyadicInterval 40),(⟨745442288544,745442307874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176360089600,176360089664⟩ : DyadicInterval 40),(⟨-210154828736,-210154828672⟩ : DyadicInterval 40),(⟨745398074102,745398093432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33794739072,-33704480000⟩ : DyadicInterval 40),(⟨778975623616,779020772416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176227072768,176421206784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210241696960,-209965806784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e642_ok : ecellOkT e642 = true := by decide +kernel
theorem e642_pos {a z : ℝ} (ha1 : ((142407/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((178221/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e642 e642_ok ha1 ha2 hz1 hz2 hz

-- box ['355593/2048000', '142407/819200', '3997/4000', '1999/2000']  interval_lower 37072873/1099511627776
noncomputable def e643 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165986,0,true,176032904512,176032904576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089566,0,false,-209689985920,-209689985856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067689,0,true,176227072768,176227072832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187863,0,false,-209965806848,-209965806784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290275985332,0,true,175910899520,175910899584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908747270220,0,false,-209516735104,-209516735040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290551499970,0,true,176145654912,176145654976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908471755582,0,false,-209850136384,-209850136320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560420066,0,true,48791168,48791232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462835486,0,false,-48793408,-48793344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584908569,0,true,73278336,73278400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438346983,0,false,-73283264,-73283200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622891,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625611,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290347571295,0,true,175971899968,175971900032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908675684257,0,false,-209603351808,-209603351744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290599292581,0,true,176186372032,176186372096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908423962971,0,false,-209907980672,-209907980608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066301887452,0,false,-33721608576,-33721608512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066389324730,0,false,-33631451840,-33631451776⟩
    { al := (355593/2048000), au := (142407/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨190907538210,191135439913⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175910899520,175910899584⟩ : DyadicInterval 40),(⟨-209516735104,-209516735040⟩ : DyadicInterval 40),(⟨745490613513,745490632843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176145654912,176145654976⟩ : DyadicInterval 40),(⟨-209850136384,-209850136320⟩ : DyadicInterval 40),(⟨745442287861,745442307191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48792290,73280793⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48791168,48791232⟩ : DyadicInterval 40),(⟨-48793408,-48793344⟩ : DyadicInterval 40),(⟨762123382506,762123401835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73278336,73278400⟩ : DyadicInterval 40),(⟨-73283264,-73283200⟩ : DyadicInterval 40),(⟨762123381131,762123400461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190835943519,191087664805⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175971899968,175971900032⟩ : DyadicInterval 40),(⟨-209603351808,-209603351744⟩ : DyadicInterval 40),(⟨745478064080,745478083410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176186372032,176186372096⟩ : DyadicInterval 40),(⟨-209907980672,-209907980608⟩ : DyadicInterval 40),(⟨745433897729,745433917059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33721608576,-33631451776⟩ : DyadicInterval 40),(⟨778939109504,778984207168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176032904512,176227072832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209965806848,-209689985856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e643_ok : ecellOkT e643 = true := by decide +kernel
theorem e643_pos {a z : ℝ} (ha1 : ((355593/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((142407/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e643 e643_ok ha1 ha2 hz1 hz2 hz

-- box ['142407/819200', '178221/1024000', '3997/4000', '1999/2000']  interval_lower 39765407/1099511627776
noncomputable def e644 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067688,0,true,176227072768,176227072832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187864,0,false,-209965806848,-209965806784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969392,0,true,176421206720,176421206784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286160,0,false,-210241696960,-210241696896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290503716108,0,true,176104943680,176104943744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908519539444,0,false,-209792305728,-209792305664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290779287722,0,true,176339706176,176339706240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908243967830,0,false,-210125859520,-210125859456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560480933,0,true,48852032,48852096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462774619,0,false,-48854272,-48854208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584999886,0,true,73369600,73369664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438255666,0,false,-73374592,-73374528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622879,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625606,0,false,-2176,-2112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290575387527,0,true,176166006208,176166006272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908447868025,0,false,-209879047552,-209879047488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290827137306,0,true,176380464640,176380464704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908196118246,0,false,-210183787264,-210183787200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066222644501,0,false,-33803322624,-33803322560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066310196006,0,false,-33713041344,-33713041280⟩
    { al := (142407/819200), au := (178221/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨191135439912,191363341616⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176104943680,176104943744⟩ : DyadicInterval 40),(⟨-209792305728,-209792305664⟩ : DyadicInterval 40),(⟨745450674351,745450693680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176339706176,176339706240⟩ : DyadicInterval 40),(⟨-210125859520,-210125859456⟩ : DyadicInterval 40),(⟨745402279830,745402299160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48853157,73372110⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48852032,48852096⟩ : DyadicInterval 40),(⟨-48854272,-48854208⟩ : DyadicInterval 40),(⟨762123382501,762123401830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73369600,73369664⟩ : DyadicInterval 40),(⟨-73374592,-73374528⟩ : DyadicInterval 40),(⟨762123381151,762123400480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-2112⟩ : DyadicInterval 40),(⟨762123384672,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191063759751,191315509530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176166006208,176166006272⟩ : DyadicInterval 40),(⟨-209879047552,-209879047488⟩ : DyadicInterval 40),(⟨745438094595,745438113925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176380464640,176380464704⟩ : DyadicInterval 40),(⟨-210183787264,-210183787200⟩ : DyadicInterval 40),(⟨745393869462,745393888792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33803322624,-33713041280⟩ : DyadicInterval 40),(⟨778979904256,779025064192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176227072768,176421206784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210241696960,-209965806784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e644_ok : ecellOkT e644 = true := by decide +kernel
theorem e644_pos {a z : ℝ} (ha1 : ((142407/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((178221/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e644 e644_ok ha1 ha2 hz1 hz2 hz

-- box ['44343/256000', '710337/4096000', '1999/2000', '3999/4000']  interval_lower 31202725/1099511627776
noncomputable def e645 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362582,0,true,175644465088,175644465152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892970,0,false,-209138551616,-209138551552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264285,0,true,175838701952,175838702016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991267,0,false,-209414234176,-209414234112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289868136714,0,true,175563295488,175563295552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909155118838,0,false,-209023381568,-209023381504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290143594377,0,true,175798076480,175798076544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908879661175,0,false,-209356564288,-209356564224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535963076,0,true,24334976,24335040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487292476,0,false,-24335616,-24335552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560360271,0,true,48731392,48731456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462895281,0,false,-48733632,-48733568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625616,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627238,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1289915744966,0,true,175603876992,175603877056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨909107510586,0,false,-209080959424,-209080959360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290167437886,0,true,175818396672,175818396736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908855817666,0,false,-209385409216,-209385409152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066451824668,0,false,-33567012480,-33567012416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066539054384,0,false,-33477082368,-33477082304⟩
    { al := (44343/256000), au := (710337/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨190451734806,190679636509⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175563295488,175563295552⟩ : DyadicInterval 40),(⟨-209023381568,-209023381504⟩ : DyadicInterval 40),(⟨745562020035,745562039364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175798076480,175798076544⟩ : DyadicInterval 40),(⟨-209356564288,-209356564224⟩ : DyadicInterval 40),(⟨745513809747,745513829077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24335300,48732495⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24334976,24335040⟩ : DyadicInterval 40),(⟨-24335616,-24335552⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48731392,48731456⟩ : DyadicInterval 40),(⟨-48733632,-48733568⟩ : DyadicInterval 40),(⟨762123382512,762123401841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190404117190,190655810110⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175603876992,175603877056⟩ : DyadicInterval 40),(⟨-209080959424,-209080959360⟩ : DyadicInterval 40),(⟨745553692811,745553712140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175818396672,175818396736⟩ : DyadicInterval 40),(⟨-209385409216,-209385409152⟩ : DyadicInterval 40),(⟨745509633344,745509652673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33567012480,-33477082304⟩ : DyadicInterval 40),(⟨778861924768,778906909120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175644465088,175838702016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209414234176,-209138551552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e645_ok : ecellOkT e645 = true := by decide +kernel
theorem e645_pos {a z : ℝ} (ha1 : ((44343/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((710337/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e645 e645_ok ha1 ha2 hz1 hz2 hz

-- box ['710337/4096000', '355593/2048000', '1999/2000', '3999/4000']  interval_lower 33865937/1099511627776
noncomputable def e646 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264284,0,true,175838701952,175838702016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991268,0,false,-209414234176,-209414234112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165987,0,true,176032904512,176032904576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089565,0,false,-209689985920,-209689985856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290095924465,0,true,175757449536,175757449600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908927331087,0,false,-209298897408,-209298897344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290371439103,0,true,175992237696,175992237760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908651816449,0,false,-209632232640,-209632232576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535993501,0,true,24365440,24365504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487262051,0,false,-24366016,-24365952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560421130,0,true,48792256,48792320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462834422,0,false,-48794496,-48794432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625610,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627237,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290143589688,0,true,175798072512,175798072576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908879665864,0,false,-209356558656,-209356558592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290395311101,0,true,176012578560,176012578624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908627944451,0,false,-209661119232,-209661119168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066372750806,0,false,-33648540672,-33648540608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066460094728,0,false,-33558486080,-33558486016⟩
    { al := (710337/4096000), au := (355593/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨190679636508,190907538211⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175757449536,175757449600⟩ : DyadicInterval 40),(⟨-209298897408,-209298897344⟩ : DyadicInterval 40),(⟨745522157972,745522177301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175992237696,175992237760⟩ : DyadicInterval 40),(⟨-209632232640,-209632232576⟩ : DyadicInterval 40),(⟨745473878840,745473898170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24365725,48793354⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24365440,24365504⟩ : DyadicInterval 40),(⟨-24366016,-24365952⟩ : DyadicInterval 40),(⟨762123383300,762123402629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48792256,48792320⟩ : DyadicInterval 40),(⟨-48794496,-48794432⟩ : DyadicInterval 40),(⟨762123382506,762123401835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190631961912,190883683325⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175798072512,175798072576⟩ : DyadicInterval 40),(⟨-209356558656,-209356558592⟩ : DyadicInterval 40),(⟨745513810569,745513829898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176012578560,176012578624⟩ : DyadicInterval 40),(⟨-209661119232,-209661119168⟩ : DyadicInterval 40),(⟨745469692338,745469711667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33648540672,-33558486016⟩ : DyadicInterval 40),(⟨778902626624,778947673216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨175838701952,176032904576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209689985920,-209414234112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e646_ok : ecellOkT e646 = true := by decide +kernel
theorem e646_pos {a z : ℝ} (ha1 : ((710337/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((355593/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e646 e646_ok ha1 ha2 hz1 hz2 hz

-- box ['44343/256000', '710337/4096000', '3999/4000', '1']  interval_lower 3834553/137438953472
noncomputable def e647 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1289963362582,0,true,175644465088,175644465152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨909059892970,0,false,-209138551616,-209138551552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264285,0,true,175838701952,175838702016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991267,0,false,-209414234176,-209414234112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1289915749648,0,true,175603881024,175603881088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨909107505904,0,false,-209080965056,-209080964992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535994289,0,true,24366208,24366272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487261263,0,false,-24366784,-24366720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627236,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1289939551238,0,true,175624169088,175624169152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨909083704314,0,false,-209109752064,-209109752000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191272777,0,true,175838709184,175838709248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨908831982775,0,false,-209414244480,-209414244416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066443558190,0,false,-33575535296,-33575535232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066530808731,0,false,-33485582976,-33485582912⟩
    { al := (44343/256000), au := (710337/4096000), zl := (3999/4000), zu := 1,
      A := ⟨190451734806,190679636509⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175644465088,175644465152⟩ : DyadicInterval 40),(⟨-209138551616,-209138551552⟩ : DyadicInterval 40),(⟨745545361757,745545381087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175603881024,175603881088⟩ : DyadicInterval 40),(⟨-209080965056,-209080964992⟩ : DyadicInterval 40),(⟨745553691955,745553711284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24366513⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24366208,24366272⟩ : DyadicInterval 40),(⟨-24366784,-24366720⟩ : DyadicInterval 40),(⟨762123383300,762123402629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨190427923462,190679645001⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175624169088,175624169152⟩ : DyadicInterval 40),(⟨-209109752064,-209109752000⟩ : DyadicInterval 40),(⟨745549527975,745549547305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838709184,175838709248⟩ : DyadicInterval 40),(⟨-209414244480,-209414244416⟩ : DyadicInterval 40),(⟨745505457897,745505477226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33575535296,-33485582912⟩ : DyadicInterval 40),(⟨778866175072,778911170528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨175644465088,175838702016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209414234176,-209138551552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e647_ok : ecellOkT e647 = true := by decide +kernel
theorem e647_pos {a z : ℝ} (ha1 : ((44343/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((710337/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e647 e647_ok ha1 ha2 hz1 hz2 hz

-- box ['710337/4096000', '355593/2048000', '3999/4000', '1']  interval_lower 16668687/549755813888
noncomputable def e648 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290191264284,0,true,175838701952,175838702016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908831991268,0,false,-209414234176,-209414234112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165987,0,true,176032904512,176032904576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089565,0,false,-209689985920,-209689985856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290143594374,0,true,175798076480,175798076544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908879661178,0,false,-209356564288,-209356564224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536024719,0,true,24396672,24396736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487230833,0,false,-24397248,-24397184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627234,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1290167424447,0,true,175818385216,175818385280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨908855831105,0,false,-209385392960,-209385392896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419174478,0,true,176032911744,176032911808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨908604081074,0,false,-209689996224,-209689996160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066364464556,0,false,-33657084416,-33657084352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066451829330,0,false,-33567007680,-33567007616⟩
    { al := (710337/4096000), au := (355593/2048000), zl := (3999/4000), zu := 1,
      A := ⟨190679636508,190907538211⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175838701952,175838702016⟩ : DyadicInterval 40),(⟨-209414234176,-209414234112⟩ : DyadicInterval 40),(⟨745505459369,745505478699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175798076480,175798076544⟩ : DyadicInterval 40),(⟨-209356564288,-209356564224⟩ : DyadicInterval 40),(⟨745513809748,745513829077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24396943⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24396672,24396736⟩ : DyadicInterval 40),(⟨-24397248,-24397184⟩ : DyadicInterval 40),(⟨762123383298,762123402627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨190655796671,190907546702⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175818385216,175818385280⟩ : DyadicInterval 40),(⟨-209385392960,-209385392896⟩ : DyadicInterval 40),(⟨745509635701,745509655031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032911744,176032911808⟩ : DyadicInterval 40),(⟨-209689996224,-209689996160⟩ : DyadicInterval 40),(⟨745465506818,745465526147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33657084416,-33567007616⟩ : DyadicInterval 40),(⟨778906887424,778951945088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨175838701952,176032904576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209689985920,-209414234112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e648_ok : ecellOkT e648 = true := by decide +kernel
theorem e648_pos {a z : ℝ} (ha1 : ((710337/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((355593/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e648 e648_ok ha1 ha2 hz1 hz2 hz

-- box ['355593/2048000', '142407/819200', '1999/2000', '3999/4000']  interval_lower 36542583/1099511627776
noncomputable def e649 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165986,0,true,176032904512,176032904576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089566,0,false,-209689985920,-209689985856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067689,0,true,176227072768,176227072832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187863,0,false,-209965806848,-209965806784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290323712216,0,true,175951569344,175951569408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908699543336,0,false,-209574482368,-209574482304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290599283830,0,true,176186364608,176186364672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908423971722,0,false,-209907970048,-209907969984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536023930,0,true,24395840,24395904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487231622,0,false,-24396480,-24396416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560481998,0,true,48853120,48853184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462773554,0,false,-48855360,-48855296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625605,0,false,-2176,-2112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627235,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290371434409,0,true,175992233664,175992233728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908651821143,0,false,-209632226944,-209632226880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290623184318,0,true,176206726144,176206726208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908400071234,0,false,-209936898432,-209936898368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066293582490,0,false,-33730172288,-33730172224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066381040643,0,false,-33639993216,-33639993152⟩
    { al := (355593/2048000), au := (142407/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨190907538210,191135439913⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175951569344,175951569408⟩ : DyadicInterval 40),(⟨-209574482368,-209574482304⟩ : DyadicInterval 40),(⟨745482247260,745482266589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176186364608,176186364672⟩ : DyadicInterval 40),(⟨-209907970048,-209907969984⟩ : DyadicInterval 40),(⟨745433899234,745433918564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24396154,48854222⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24395840,24395904⟩ : DyadicInterval 40),(⟨-24396480,-24396416⟩ : DyadicInterval 40),(⟨762123383330,762123402659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48853120,48853184⟩ : DyadicInterval 40),(⟨-48855360,-48855296⟩ : DyadicInterval 40),(⟨762123382501,762123401830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2176,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨190859806633,191111556542⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175992233664,175992233728⟩ : DyadicInterval 40),(⟨-209632226944,-209632226880⟩ : DyadicInterval 40),(⟨745473879676,745473899006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176206726144,176206726208⟩ : DyadicInterval 40),(⟨-209936898432,-209936898368⟩ : DyadicInterval 40),(⟨745429702659,745429721988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33730172288,-33639993152⟩ : DyadicInterval 40),(⟨778943380192,778988489024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176032904512,176227072832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209965806848,-209689985856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e649_ok : ecellOkT e649 = true := by decide +kernel
theorem e649_pos {a z : ℝ} (ha1 : ((355593/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((142407/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e649 e649_ok ha1 ha2 hz1 hz2 hz

-- box ['142407/819200', '178221/1024000', '1999/2000', '3999/4000']  interval_lower 39232783/1099511627776
noncomputable def e650 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067688,0,true,176227072768,176227072832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187864,0,false,-209965806848,-209965806784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969392,0,true,176421206720,176421206784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286160,0,false,-210241696960,-210241696896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290551499968,0,true,176145654912,176145654976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908471755584,0,false,-209850136384,-209850136320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290827128557,0,true,176380457216,176380457280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908196126995,0,false,-210183776704,-210183776640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536054363,0,true,24426304,24426368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487201189,0,false,-24426880,-24426816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560542878,0,true,48913984,48914048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462712674,0,false,-48916224,-48916160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625599,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627234,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290599279132,0,true,176186360576,176186360640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908423976420,0,false,-209907964416,-209907964352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1290851057528,0,true,176400839424,176400839488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨908172198024,0,false,-210212746816,-210212746752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066214319723,0,false,-33811907328,-33811907264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066301892128,0,false,-33721603776,-33721603712⟩
    { al := (142407/819200), au := (178221/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨191135439912,191363341616⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176145654912,176145654976⟩ : DyadicInterval 40),(⟨-209850136384,-209850136320⟩ : DyadicInterval 40),(⟨745442287862,745442307191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176380457216,176380457280⟩ : DyadicInterval 40),(⟨-210183776704,-210183776640⟩ : DyadicInterval 40),(⟨745393870997,745393890326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24426587,48915102⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24426304,24426368⟩ : DyadicInterval 40),(⟨-24426880,-24426816⟩ : DyadicInterval 40),(⟨762123383297,762123402626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48913984,48914048⟩ : DyadicInterval 40),(⟨-48916224,-48916160⟩ : DyadicInterval 40),(⟨762123382495,762123401824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191087651356,191339429752⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176186360576,176186360640⟩ : DyadicInterval 40),(⟨-209907964416,-209907964352⟩ : DyadicInterval 40),(⟨745433900099,745433919428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176400839424,176400839488⟩ : DyadicInterval 40),(⟨-210212746816,-210212746752⟩ : DyadicInterval 40),(⟨745389664297,745389683627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33811907328,-33721603712⟩ : DyadicInterval 40),(⟨778984185472,779029356544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176227072768,176421206784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210241696960,-209965806784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e650_ok : ecellOkT e650 = true := by decide +kernel
theorem e650_pos {a z : ℝ} (ha1 : ((142407/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((178221/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e650 e650_ok ha1 ha2 hz1 hz2 hz

-- box ['355593/2048000', '142407/819200', '3999/4000', '1']  interval_lower 36012241/1099511627776
noncomputable def e651 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290419165986,0,true,176032904512,176032904576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908604089566,0,false,-209689985920,-209689985856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067689,0,true,176227072768,176227072832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187863,0,false,-209965806848,-209965806784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290371439101,0,true,175992237696,175992237760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908651816451,0,false,-209632232640,-209632232576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536055153,0,true,24427072,24427136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487200399,0,false,-24427712,-24427648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627233,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1290395297656,0,true,176012567104,176012567168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨908627957896,0,false,-209661102976,-209661102912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647076178,0,true,176227080000,176227080064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨908376179374,0,false,-209965817088,-209965817024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066285276446,0,false,-33738737088,-33738737024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066372755475,0,false,-33648535872,-33648535808⟩
    { al := (355593/2048000), au := (142407/819200), zl := (3999/4000), zu := 1,
      A := ⟨190907538210,191135439913⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176032904512,176032904576⟩ : DyadicInterval 40),(⟨-209689985920,-209689985856⟩ : DyadicInterval 40),(⟨745465508294,745465527624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175992237696,175992237760⟩ : DyadicInterval 40),(⟨-209632232640,-209632232576⟩ : DyadicInterval 40),(⟨745473878841,745473898171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24427377⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24427072,24427136⟩ : DyadicInterval 40),(⟨-24427712,-24427648⟩ : DyadicInterval 40),(⟨762123383329,762123402658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨190883669880,191135448402⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176012567104,176012567168⟩ : DyadicInterval 40),(⟨-209661102976,-209661102912⟩ : DyadicInterval 40),(⟨745469694701,745469714030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227080000,176227080064⟩ : DyadicInterval 40),(⟨-209965817088,-209965817024⟩ : DyadicInterval 40),(⟨745425507016,745425526345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33738737088,-33648535808⟩ : DyadicInterval 40),(⟨778947651520,778992771424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨176032904512,176227072832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-209965806848,-209689985856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e651_ok : ecellOkT e651 = true := by decide +kernel
theorem e651_pos {a z : ℝ} (ha1 : ((355593/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((142407/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e651 e651_ok ha1 ha2 hz1 hz2 hz

-- box ['142407/819200', '178221/1024000', '3999/4000', '1']  interval_lower 19350049/549755813888
noncomputable def e652 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290647067688,0,true,176227072768,176227072832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908376187864,0,false,-209965806848,-209965806784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969392,0,true,176421206720,176421206784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286160,0,false,-210241696960,-210241696896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290599283828,0,true,176186364608,176186364672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908423971724,0,false,-209907970048,-209907969984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536085594,0,true,24457536,24457600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487169958,0,false,-24458112,-24458048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627231,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1290623170867,0,true,176206714688,176206714752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨908400084685,0,false,-209936882176,-209936882112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874977878,0,true,176421213952,176421214016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨908148277674,0,false,-210241707200,-210241707136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066205993858,0,false,-33820493248,-33820493184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066293587167,0,false,-33730167424,-33730167360⟩
    { al := (142407/819200), au := (178221/1024000), zl := (3999/4000), zu := 1,
      A := ⟨191135439912,191363341616⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176227072768,176227072832⟩ : DyadicInterval 40),(⟨-209965806848,-209965806784⟩ : DyadicInterval 40),(⟨745425508521,745425527851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176186364608,176186364672⟩ : DyadicInterval 40),(⟨-209907970048,-209907969984⟩ : DyadicInterval 40),(⟨745433899234,745433918564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24457818⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24457536,24457600⟩ : DyadicInterval 40),(⟨-24458112,-24458048⟩ : DyadicInterval 40),(⟨762123383295,762123402624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨191111543091,191363350102⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176206714688,176206714752⟩ : DyadicInterval 40),(⟨-209936882176,-209936882112⟩ : DyadicInterval 40),(⟨745429705029,745429724358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421213952,176421214016⟩ : DyadicInterval 40),(⟨-210241707200,-210241707136⟩ : DyadicInterval 40),(⟨745385458532,745385477861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33820493248,-33730167360⟩ : DyadicInterval 40),(⟨778988467296,779033649504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨176227072768,176421206784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210241696960,-209965806784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e652_ok : ecellOkT e652 = true := by decide +kernel
theorem e652_pos {a z : ℝ} (ha1 : ((142407/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((178221/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e652 e652_ok ha1 ha2 hz1 hz2 hz

-- box ['178221/1024000', '713733/4096000', '999/1000', '3997/4000']  interval_lower 43005239/1099511627776
noncomputable def e653 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969391,0,true,176421206720,176421206784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286161,0,false,-210241696960,-210241696896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871094,0,true,176615306432,176615306496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384458,0,false,-210517656320,-210517656256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290683606049,0,true,176258199616,176258199680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908339649503,0,false,-210010034304,-210010034240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1290959177662,0,true,176492929344,176492929408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908064077890,0,false,-210343654144,-210343654080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584998542,0,true,73368256,73368320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438257010,0,false,-73373248,-73373184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609578390,0,true,97946240,97946304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413677162,0,false,-97955008,-97954944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619050,0,false,-8768,-8704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622880,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290779283809,0,true,176339702848,176339702912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908243971743,0,false,-210125854784,-210125854720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291031033460,0,true,176554127360,176554127424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907992222092,0,false,-210430662784,-210430662720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066151650648,0,false,-33876535424,-33876535360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066239295479,0,false,-33786151872,-33786151808⟩
    { al := (178221/1024000), au := (713733/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨191363341615,191591243318⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176258199616,176258199680⟩ : DyadicInterval 40),(⟨-210010034304,-210010034240⟩ : DyadicInterval 40),(⟨745419091029,745419110358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176492929344,176492929408⟩ : DyadicInterval 40),(⟨-210343654144,-210343654080⟩ : DyadicInterval 40),(⟨745370650039,745370669368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73370766,97950614⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73368256,73368320⟩ : DyadicInterval 40),(⟨-73373248,-73373184⟩ : DyadicInterval 40),(⟨762123381151,762123400481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨97946240,97946304⟩ : DyadicInterval 40),(⟨-97955008,-97954944⟩ : DyadicInterval 40),(⟨762123379209,762123398539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8768,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123407264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191267656033,191519405684⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176339702848,176339702912⟩ : DyadicInterval 40),(⟨-210125854784,-210125854720⟩ : DyadicInterval 40),(⟨745402280516,745402299845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176554127360,176554127424⟩ : DyadicInterval 40),(⟨-210430662784,-210430662720⟩ : DyadicInterval 40),(⟨745358007234,745358026564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33876535424,-33786151808⟩ : DyadicInterval 40),(⟨779016459520,779061670592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176421206720,176615306496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210517656320,-210241696896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e653_ok : ecellOkT e653 = true := by decide +kernel
theorem e653_pos {a z : ℝ} (ha1 : ((178221/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((713733/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e653 e653_ok ha1 ha2 hz1 hz2 hz

-- box ['713733/4096000', '357291/2048000', '999/1000', '3997/4000']  interval_lower 45727117/1099511627776
noncomputable def e654 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871093,0,true,176615306432,176615306496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384459,0,false,-210517656320,-210517656256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772796,0,true,176809371904,176809371968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482756,0,false,-210793684928,-210793684864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290911279849,0,true,176452133952,176452134016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908111975703,0,false,-210285659584,-210285659520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291186908438,0,true,176686870848,176686870912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907836347114,0,false,-210619432064,-210619432000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585089870,0,true,73459584,73459648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438165682,0,false,-73464576,-73464512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609700183,0,true,98068032,98068096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413555369,0,false,-98076800,-98076736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619028,0,false,-8768,-8704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622868,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291007071556,0,true,176533719872,176533719936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908016183996,0,false,-210401647040,-210401646976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291258849706,0,true,176748130816,176748130880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907764405846,0,false,-210706566080,-210706566016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066072238697,0,false,-33958435200,-33958435136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066159997778,0,false,-33867927168,-33867927104⟩
    { al := (713733/4096000), au := (357291/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨191591243317,191819145020⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176452133952,176452134016⟩ : DyadicInterval 40),(⟨-210285659584,-210285659520⟩ : DyadicInterval 40),(⟨745379074826,745379094156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176686870848,176686870912⟩ : DyadicInterval 40),(⟨-210619432064,-210619432000⟩ : DyadicInterval 40),(⟨745330564920,745330584250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73462094,98072407⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73459584,73459648⟩ : DyadicInterval 40),(⟨-73464576,-73464512⟩ : DyadicInterval 40),(⟨762123381139,762123400468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98068032,98068096⟩ : DyadicInterval 40),(⟨-98076800,-98076736⟩ : DyadicInterval 40),(⟨762123379187,762123398517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8768,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123407264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191495443780,191747221930⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176533719872,176533719936⟩ : DyadicInterval 40),(⟨-210401647040,-210401646976⟩ : DyadicInterval 40),(⟨745362223805,745362243135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176748130816,176748130880⟩ : DyadicInterval 40),(⟨-210706566080,-210706566016⟩ : DyadicInterval 40),(⟨745317891737,745317911067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33958435200,-33867927104⟩ : DyadicInterval 40),(⟨779057347168,779102620480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176615306432,176809371968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210793684928,-210517656256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e654_ok : ecellOkT e654 = true := by decide +kernel
theorem e654_pos {a z : ℝ} (ha1 : ((713733/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((357291/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e654 e654_ok ha1 ha2 hz1 hz2 hz

-- box ['178221/1024000', '713733/4096000', '3997/4000', '1999/2000']  interval_lower 42471345/1099511627776
noncomputable def e655 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969391,0,true,176421206720,176421206784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286161,0,false,-210241696960,-210241696896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871094,0,true,176615306432,176615306496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384458,0,false,-210517656320,-210517656256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290731446884,0,true,176298953664,176298953728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908291808668,0,false,-210067945344,-210067945280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291007075473,0,true,176533723264,176533723328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨908016180079,0,false,-210401651840,-210401651776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560541810,0,true,48912896,48912960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462713742,0,false,-48915136,-48915072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585091217,0,true,73460928,73460992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438164335,0,false,-73465920,-73465856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622867,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625600,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290803203767,0,true,176360078144,176360078208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908220051785,0,false,-210154812416,-210154812352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291054982037,0,true,176574523072,176574523136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907968273515,0,false,-210459663104,-210459663040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066143307119,0,false,-33885140032,-33885139968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066230972874,0,false,-33794734208,-33794734144⟩
    { al := (178221/1024000), au := (713733/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨191363341615,191591243318⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176298953664,176298953728⟩ : DyadicInterval 40),(⟨-210067945344,-210067945280⟩ : DyadicInterval 40),(⟨745410686478,745410705808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176533723264,176533723328⟩ : DyadicInterval 40),(⟨-210401651840,-210401651776⟩ : DyadicInterval 40),(⟨745362223107,745362242436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48914034,73463441⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48912896,48912960⟩ : DyadicInterval 40),(⟨-48915136,-48915072⟩ : DyadicInterval 40),(⟨762123382495,762123401825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73460928,73460992⟩ : DyadicInterval 40),(⟨-73465920,-73465856⟩ : DyadicInterval 40),(⟨762123381139,762123400468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191291575991,191543354261⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176360078144,176360078208⟩ : DyadicInterval 40),(⟨-210154812416,-210154812352⟩ : DyadicInterval 40),(⟨745398076451,745398095780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176574523072,176574523136⟩ : DyadicInterval 40),(⟨-210459663104,-210459663040⟩ : DyadicInterval 40),(⟨745353792477,745353811806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33885140032,-33794734144⟩ : DyadicInterval 40),(⟨779020750688,779065972896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176421206720,176615306496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210517656320,-210241696896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e655_ok : ecellOkT e655 = true := by decide +kernel
theorem e655_pos {a z : ℝ} (ha1 : ((178221/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((713733/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e655 e655_ok ha1 ha2 hz1 hz2 hz

-- box ['713733/4096000', '357291/2048000', '3997/4000', '1999/2000']  interval_lower 45190919/1099511627776
noncomputable def e656 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871093,0,true,176615306432,176615306496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384459,0,false,-210517656320,-210517656256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772796,0,true,176809371904,176809371968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482756,0,false,-210793684928,-210793684864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290959177660,0,true,176492929344,176492929408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908064077892,0,false,-210343654144,-210343654080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291234863224,0,true,176727706048,176727706112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907788392328,0,false,-210677513280,-210677513216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560602696,0,true,48973824,48973888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462652856,0,false,-48976064,-48976000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585182562,0,true,73552320,73552384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438072990,0,false,-73557248,-73557184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622855,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625595,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291031020000,0,true,176554115904,176554115968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907992235552,0,false,-210430646464,-210430646400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291282826768,0,true,176768547200,176768547264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907740428784,0,false,-210735608192,-210735608128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066063875306,0,false,-33967060992,-33967060928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066151655339,0,false,-33876530560,-33876530496⟩
    { al := (713733/4096000), au := (357291/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨191591243317,191819145020⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176492929344,176492929408⟩ : DyadicInterval 40),(⟨-210343654144,-210343654080⟩ : DyadicInterval 40),(⟨745370650039,745370669368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176727706048,176727706112⟩ : DyadicInterval 40),(⟨-210677513280,-210677513216⟩ : DyadicInterval 40),(⟨745322117729,745322137058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48974920,73554786⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48973824,48973888⟩ : DyadicInterval 40),(⟨-48976064,-48976000⟩ : DyadicInterval 40),(⟨762123382490,762123401819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73552320,73552384⟩ : DyadicInterval 40),(⟨-73557248,-73557184⟩ : DyadicInterval 40),(⟨762123381095,762123400424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191519392224,191771198992⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176554115904,176554115968⟩ : DyadicInterval 40),(⟨-210430646464,-210430646400⟩ : DyadicInterval 40),(⟨745358009590,745358028919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176768547200,176768547264⟩ : DyadicInterval 40),(⟨-210735608192,-210735608128⟩ : DyadicInterval 40),(⟨745313666838,745313686167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33967060992,-33876530496⟩ : DyadicInterval 40),(⟨779061648864,779106933376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176615306432,176809371968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210793684928,-210517656256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e656_ok : ecellOkT e656 = true := by decide +kernel
theorem e656_pos {a z : ℝ} (ha1 : ((713733/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((357291/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e656 e656_ok ha1 ha2 hz1 hz2 hz

-- box ['357291/2048000', '715431/4096000', '999/1000', '3997/4000']  interval_lower 48462663/1099511627776
noncomputable def e657 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772795,0,true,176809371904,176809371968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482757,0,false,-210793684928,-210793684864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674498,0,true,177003403072,177003403136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581054,0,false,-211069782912,-211069782848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291138953649,0,true,176646034176,176646034240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907884301903,0,false,-210561353920,-210561353856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291414639214,0,true,176880778176,176880778240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907608616338,0,false,-210895279232,-210895279168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585181212,0,true,73550912,73550976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438074340,0,false,-73555904,-73555840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609821995,0,true,98189824,98189888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413433557,0,false,-98198656,-98198592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619006,0,false,-8832,-8768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622856,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291234859315,0,true,176727702720,176727702784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907788396237,0,false,-210677508544,-210677508480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291486665944,0,true,176942100096,176942100160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907536589608,0,false,-210982538624,-210982538560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065992732342,0,false,-34040438528,-34040438464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066080605691,0,false,-33949805824,-33949805760⟩
    { al := (357291/2048000), au := (715431/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨191819145019,192047046722⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176646034176,176646034240⟩ : DyadicInterval 40),(⟨-210561353920,-210561353856⟩ : DyadicInterval 40),(⟨745339009931,745339029261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176880778176,176880778240⟩ : DyadicInterval 40),(⟨-210895279232,-210895279168⟩ : DyadicInterval 40),(⟨745290431165,745290450495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73553436,98194219⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73550912,73550976⟩ : DyadicInterval 40),(⟨-73555904,-73555840⟩ : DyadicInterval 40),(⟨762123381127,762123400456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98189824,98189888⟩ : DyadicInterval 40),(⟨-98198656,-98198592⟩ : DyadicInterval 40),(⟨762123379198,762123398527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8832,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123407296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191723231539,191975038168⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176727702720,176727702784⟩ : DyadicInterval 40),(⟨-210677508544,-210677508480⟩ : DyadicInterval 40),(⟨745322118416,745322137746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176942100096,176942100160⟩ : DyadicInterval 40),(⟨-210982538624,-210982538560⟩ : DyadicInterval 40),(⟨745277727529,745277746858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34040438528,-33949805760⟩ : DyadicInterval 40),(⟨779098286496,779143622144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176809371904,177003403136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211069782912,-210793684864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e657_ok : ecellOkT e657 = true := by decide +kernel
theorem e657_pos {a z : ℝ} (ha1 : ((357291/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((715431/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e657 e657_ok ha1 ha2 hz1 hz2 hz

-- box ['715431/4096000', '17907/102400', '999/1000', '3997/4000']  interval_lower 51211857/1099511627776
noncomputable def e658 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674497,0,true,177003403072,177003403136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581055,0,false,-211069782912,-211069782848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576200,0,true,177197400064,177197400128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679352,0,false,-211345950208,-211345950144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291366627450,0,true,176839900160,176839900224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907656628102,0,false,-210837117504,-210837117440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291642369989,0,true,177074651264,177074651328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907380885563,0,false,-211171195584,-211171195520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585272570,0,true,73642304,73642368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437982982,0,false,-73647296,-73647232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099609943826,0,true,98311616,98311680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413311726,0,false,-98320448,-98320384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618984,0,false,-8832,-8768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622844,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291462647058,0,true,176921651328,176921651392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907560608494,0,false,-210953439296,-210953439232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291714482186,0,true,177136035136,177136035200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907308773366,0,false,-211258580416,-211258580352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065913131579,0,false,-34122545280,-34122545216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066001119227,0,false,-34031787968,-34031787904⟩
    { al := (715431/4096000), au := (17907/102400), zl := (999/1000), zu := (3997/4000),
      A := ⟨192047046721,192274948424⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176839900160,176839900224⟩ : DyadicInterval 40),(⟨-210837117504,-210837117440⟩ : DyadicInterval 40),(⟨745298896487,745298915817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177074651264,177074651328⟩ : DyadicInterval 40),(⟨-211171195584,-211171195520⟩ : DyadicInterval 40),(⟨745250248774,745250268103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73644794,98316050⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73642304,73642368⟩ : DyadicInterval 40),(⟨-73647296,-73647232⟩ : DyadicInterval 40),(⟨762123381115,762123400444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98311616,98311680⟩ : DyadicInterval 40),(⟨-98320448,-98320384⟩ : DyadicInterval 40),(⟨762123379176,762123398506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8832,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123407296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191951019282,192202854410⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176921651328,176921651392⟩ : DyadicInterval 40),(⟨-210953439296,-210953439232⟩ : DyadicInterval 40),(⟨745281964380,745281983710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177136035136,177136035200⟩ : DyadicInterval 40),(⟨-211258580416,-211258580352⟩ : DyadicInterval 40),(⟨745237514633,745237533962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34122545280,-34031787904⟩ : DyadicInterval 40),(⟨779139277568,779184675520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177003403072,177197400128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211345950208,-211069782848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e658_ok : ecellOkT e658 = true := by decide +kernel
theorem e658_pos {a z : ℝ} (ha1 : ((715431/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17907/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e658 e658_ok ha1 ha2 hz1 hz2 hz

-- box ['357291/2048000', '715431/4096000', '3997/4000', '1999/2000']  interval_lower 47924269/1099511627776
noncomputable def e659 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772795,0,true,176809371904,176809371968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482757,0,false,-210793684928,-210793684864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674498,0,true,177003403072,177003403136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581054,0,false,-211069782912,-211069782848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291186908436,0,true,176686870848,176686870912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907836347116,0,false,-210619432064,-210619432000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291462650975,0,true,176921654656,176921654720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907560604577,0,false,-210953444032,-210953443968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560663593,0,true,49034688,49034752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462591959,0,false,-49036928,-49036864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585273923,0,true,73643648,73643712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437981629,0,false,-73648640,-73648576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622843,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625590,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291258836241,0,true,176748119360,176748119424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907764419311,0,false,-210706549760,-210706549696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291510671491,0,true,176962537088,176962537152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907512584061,0,false,-211011622528,-211011622464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065984349067,0,false,-34049085440,-34049085376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066072243394,0,false,-33958430400,-33958430336⟩
    { al := (357291/2048000), au := (715431/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨191819145019,192047046722⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176686870848,176686870912⟩ : DyadicInterval 40),(⟨-210619432064,-210619432000⟩ : DyadicInterval 40),(⟨745330564921,745330584250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176921654656,176921654720⟩ : DyadicInterval 40),(⟨-210953444032,-210953443968⟩ : DyadicInterval 40),(⟨745281963689,745281983018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49035817,73646147⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49034688,49034752⟩ : DyadicInterval 40),(⟨-49036928,-49036864⟩ : DyadicInterval 40),(⟨762123382485,762123401814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73643648,73643712⟩ : DyadicInterval 40),(⟨-73648640,-73648576⟩ : DyadicInterval 40),(⟨762123381114,762123400444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191747208465,191999043715⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176748119360,176748119424⟩ : DyadicInterval 40),(⟨-210706549760,-210706549696⟩ : DyadicInterval 40),(⟨745317894100,745317913429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176962537088,176962537152⟩ : DyadicInterval 40),(⟨-211011622528,-211011622464⟩ : DyadicInterval 40),(⟨745273492499,745273511829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34049085440,-33958430336⟩ : DyadicInterval 40),(⟨779102598784,779147945600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176809371904,177003403136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211069782912,-210793684864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e659_ok : ecellOkT e659 = true := by decide +kernel
theorem e659_pos {a z : ℝ} (ha1 : ((357291/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((715431/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e659 e659_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B010

end


