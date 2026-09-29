-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B037
-- name    : CK_CKLaneC2R_EpCells_B037
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:18:27.413483+00:00
-- url     : https://prove2.me/theorems/1b5130c1-357d-4618-9906-5b271c7b08c3
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B037` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B037` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B037` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B037 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B037.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B037 =====
section

namespace CKLaneC2R.EpCells.B037

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['650907/4096000', '1302663/8192000', '1999/2000', '7997/8000']  interval_lower 203602611/1099511627776
noncomputable def e2220 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274150781875,0,true,162083183616,162083183680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924872473677,0,false,-190177604608,-190177604544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274286530811,0,true,162200320128,162200320192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924736724741,0,false,-190338998208,-190338998144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544998925,0,true,33370624,33370688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478256627,0,false,-33371712,-33371648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556153453,0,true,44524736,44524800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467102099,0,false,-44526592,-44526528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625972,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626764,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274194459111,0,true,162120873664,162120873728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924828796441,0,false,-190229530432,-190229530368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274319317876,0,true,162228609920,162228609984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924703937676,0,false,-190377982656,-190377982592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071719535590,0,false,-28149372672,-28149372608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071759223170,0,false,-28108656704,-28108656640⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162083183616,162083183680⟩ : DyadicInterval 40),(⟨-190177604608,-190177604544⟩ : DyadicInterval 40),(⟨748195207283,748195226612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162200320128,162200320192⟩ : DyadicInterval 40),(⟨-190338998208,-190338998144⟩ : DyadicInterval 40),(⟨748173453116,748173472446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33371149,44525677⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33370624,33370688⟩ : DyadicInterval 40),(⟨-33371712,-33371648⟩ : DyadicInterval 40),(⟨762123383083,762123402412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44524736,44524800⟩ : DyadicInterval 40),(⟨-44526592,-44526528⟩ : DyadicInterval 40),(⟨762123382676,762123402005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174682831335,174807690100⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162120873664,162120873728⟩ : DyadicInterval 40),(⟨-190229530432,-190229530368⟩ : DyadicInterval 40),(⟨748188209753,748188229083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162228609920,162228609984⟩ : DyadicInterval 40),(⟨-190377982656,-190377982592⟩ : DyadicInterval 40),(⟨748168196289,748168215619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28149372672,-28108656640⟩ : DyadicInterval 40),(⟨776177711936,776198089216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2220_ok : ecellOkT e2220 = true := by decide +kernel
theorem e2220_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2220 e2220_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '1999/2000', '7997/8000']  interval_lower 51191165/274877906944
noncomputable def e2221 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274264675750,0,true,162181462464,162181462528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924758579802,0,false,-190313012800,-190313012736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274400438930,0,true,162298600832,162298600896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924622816622,0,false,-190474443200,-190474443136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545021503,0,true,33393216,33393280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478234049,0,false,-33394240,-33394176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556183560,0,true,44554880,44554944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467071992,0,false,-44556736,-44556672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625970,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626762,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274308381474,0,true,162219173760,162219173824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924714874078,0,false,-190364978944,-190364978880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274433247368,0,true,162326906496,162326906560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924590008184,0,false,-190513457920,-190513457856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071683297244,0,false,-28186551424,-28186551360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071723012967,0,false,-28145805120,-28145805056⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162181462464,162181462528⟩ : DyadicInterval 40),(⟨-190313012800,-190313012736⟩ : DyadicInterval 40),(⟨748176956579,748176975908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162298600832,162298600896⟩ : DyadicInterval 40),(⟨-190474443200,-190474443136⟩ : DyadicInterval 40),(⟨748155185673,748155205003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33393727,44555784⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33393216,33393280⟩ : DyadicInterval 40),(⟨-33394240,-33394176⟩ : DyadicInterval 40),(⟨762123383049,762123402378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44554880,44554944⟩ : DyadicInterval 40),(⟨-44556736,-44556672⟩ : DyadicInterval 40),(⟨762123382674,762123402003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174796753698,174921619592⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162219173760,162219173824⟩ : DyadicInterval 40),(⟨-190364978944,-190364978880⟩ : DyadicInterval 40),(⟨748169949840,748169969170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162326906496,162326906560⟩ : DyadicInterval 40),(⟨-190513457920,-190513457856⟩ : DyadicInterval 40),(⟨748149921977,748149941306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28186551424,-28145805056⟩ : DyadicInterval 40),(⟨776196286144,776216678592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2221_ok : ecellOkT e2221 = true := by decide +kernel
theorem e2221_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2221 e2221_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '7997/8000', '3999/4000']  interval_lower 203436249/1099511627776
noncomputable def e2222 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274172622689,0,true,162102030720,162102030784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924850632863,0,false,-190203569792,-190203569728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274308385870,0,true,162219177536,162219177600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924714869682,0,false,-190364984128,-190364984064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533875175,0,true,22247168,22247232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489380377,0,false,-22247680,-22247616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545022175,0,true,33393856,33393920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478233377,0,false,-33394944,-33394880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626761,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627326,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274205379433,0,true,162130296896,162130296960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924817876119,0,false,-190242513472,-190242513408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274330245347,0,true,162238038400,162238038464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924693010205,0,false,-190390976000,-190390975936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071716060837,0,false,-28152937536,-28152937472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071755753171,0,false,-28112216512,-28112216448⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162102030720,162102030784⟩ : DyadicInterval 40),(⟨-190203569792,-190203569728⟩ : DyadicInterval 40),(⟨748191708362,748191727691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162219177536,162219177600⟩ : DyadicInterval 40),(⟨-190364984128,-190364984064⟩ : DyadicInterval 40),(⟨748169949127,748169968457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22247399,33394399⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22247168,22247232⟩ : DyadicInterval 40),(⟨-22247680,-22247616⟩ : DyadicInterval 40),(⟨762123383357,762123402686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33393856,33393920⟩ : DyadicInterval 40),(⟨-33394944,-33394880⟩ : DyadicInterval 40),(⟨762123383081,762123402410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174693751657,174818617571⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162130296896,162130296960⟩ : DyadicInterval 40),(⟨-190242513472,-190242513408⟩ : DyadicInterval 40),(⟨748186459901,748186479231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162238038400,162238038464⟩ : DyadicInterval 40),(⟨-190390976000,-190390975936⟩ : DyadicInterval 40),(⟨748166444038,748166463367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28152937536,-28112216448⟩ : DyadicInterval 40),(⟨776179491840,776199871648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2222_ok : ecellOkT e2222 = true := by decide +kernel
theorem e2222_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2222 e2222_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '7997/8000', '3999/4000']  interval_lower 204598067/1099511627776
noncomputable def e2223 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274286530809,0,true,162200320128,162200320192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924736724743,0,false,-190338998144,-190338998080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274422308233,0,true,162317468800,162317468864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924600947319,0,false,-190500449344,-190500449280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533890227,0,true,22262208,22262272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489365325,0,false,-22262720,-22262656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545044756,0,true,33416448,33416512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478210796,0,false,-33417536,-33417472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626760,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627326,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274319308914,0,true,162228602240,162228602304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924703946638,0,false,-190377972032,-190377971968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274444181954,0,true,162336340224,162336340288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924579073598,0,false,-190526461312,-190526461248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071679817963,0,false,-28190121024,-28190120960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071719538441,0,false,-28149369792,-28149369728⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162200320128,162200320192⟩ : DyadicInterval 40),(⟨-190338998144,-190338998080⟩ : DyadicInterval 40),(⟨748173453090,748173472420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162317468800,162317468864⟩ : DyadicInterval 40),(⟨-190500449344,-190500449280⟩ : DyadicInterval 40),(⟨748151677136,748151696466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22262451,33416980⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22262208,22262272⟩ : DyadicInterval 40),(⟨-22262720,-22262656⟩ : DyadicInterval 40),(⟨762123383357,762123402686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33416448,33416512⟩ : DyadicInterval 40),(⟨-33417536,-33417472⟩ : DyadicInterval 40),(⟨762123383080,762123402409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174807681138,174932554178⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162228602240,162228602304⟩ : DyadicInterval 40),(⟨-190377972032,-190377971968⟩ : DyadicInterval 40),(⟨748168197709,748168217039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162336340224,162336340288⟩ : DyadicInterval 40),(⟨-190526461312,-190526461248⟩ : DyadicInterval 40),(⟨748148167444,748148186773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28190121024,-28149369728⟩ : DyadicInterval 40),(⟨776198068480,776218463392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2223_ok : ecellOkT e2223 = true := by decide +kernel
theorem e2223_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2223 e2223_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '3999/4000', '7999/8000']  interval_lower 200955267/1099511627776
noncomputable def e2224 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273966618778,0,true,161924251008,161924251072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925056636774,0,false,-189958688640,-189958688576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274102367714,0,true,162041404480,162041404544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924920887838,0,false,-190120050112,-190120050048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522736322,0,true,11108480,11108544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500519230,0,false,-11108608,-11108544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533860742,0,true,22232704,22232768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489394810,0,false,-22233216,-22233152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627326,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273988426569,0,true,161943072320,161943072384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925034828983,0,false,-189984609472,-189984609408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274113285379,0,true,162050826048,162050826112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924909970173,0,false,-190133028736,-190133028672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071785009823,0,false,-28082202624,-28082202560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071824650624,0,false,-28041537088,-28041537024⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161924251008,161924251072⟩ : DyadicInterval 40),(⟨-189958688640,-189958688576⟩ : DyadicInterval 40),(⟨748224692467,748224711797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162041404480,162041404544⟩ : DyadicInterval 40),(⟨-190120050112,-190120050048⟩ : DyadicInterval 40),(⟨748202961612,748202980942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11108546,22232966⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11108480,11108544⟩ : DyadicInterval 40),(⟨-11108608,-11108544⟩ : DyadicInterval 40),(⟨762123383503,762123402832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22232704,22232768⟩ : DyadicInterval 40),(⟨-22233216,-22233152⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174476798793,174601657603⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161943072320,161943072384⟩ : DyadicInterval 40),(⟨-189984609472,-189984609408⟩ : DyadicInterval 40),(⟨748221202622,748221221952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162050826048,162050826112⟩ : DyadicInterval 40),(⟨-190133028736,-190133028672⟩ : DyadicInterval 40),(⟨748201213170,748201232499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28082202624,-28041537024⟩ : DyadicInterval 40),(⟨776144152128,776164504192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2224_ok : ecellOkT e2224 = true := by decide +kernel
theorem e2224_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2224 e2224_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '3999/4000', '7999/8000']  interval_lower 202110911/1099511627776
noncomputable def e2225 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274080541141,0,true,162022568640,162022568704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924942714411,0,false,-190094103808,-190094103744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274216304321,0,true,162139723904,162139723968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924806951231,0,false,-190255502080,-190255502016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522743847,0,true,11115968,11116032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500511705,0,false,-11116160,-11116096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533875794,0,true,22247744,22247808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489379758,0,false,-22248256,-22248192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627325,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274102363171,0,true,162041400576,162041400640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924920892381,0,false,-190120044736,-190120044672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274227229109,0,true,162149150784,162149150848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924796026443,0,false,-190268490752,-190268490688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071748809650,0,false,-28119339904,-28119339840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071788478593,0,false,-28078644096,-28078644032⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162022568640,162022568704⟩ : DyadicInterval 40),(⟨-190094103808,-190094103744⟩ : DyadicInterval 40),(⟨748206456805,748206476135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162139723904,162139723968⟩ : DyadicInterval 40),(⟨-190255502080,-190255502016⟩ : DyadicInterval 40),(⟨748184709249,748184728578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11116071,22248018⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11115968,11116032⟩ : DyadicInterval 40),(⟨-11116160,-11116096⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22247744,22247808⟩ : DyadicInterval 40),(⟨-22248256,-22248192⟩ : DyadicInterval 40),(⟨762123383357,762123402686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174590735395,174715601333⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162041400576,162041400640⟩ : DyadicInterval 40),(⟨-190120044736,-190120044672⟩ : DyadicInterval 40),(⟨748202962341,748202981670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162149150784,162149150848⟩ : DyadicInterval 40),(⟨-190268490752,-190268490688⟩ : DyadicInterval 40),(⟨748182958490,748182977820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28119339904,-28078644032⟩ : DyadicInterval 40),(⟨776162705632,776183072832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2225_ok : ecellOkT e2225 = true := by decide +kernel
theorem e2225_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2225 e2225_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '7999/8000', '1']  interval_lower 100394897/549755813888
noncomputable def e2226 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273988431104,0,true,161943076288,161943076352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925034824448,0,false,-189984614848,-189984614784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522744414,0,true,11116544,11116608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500511138,0,false,-11116736,-11116672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273999332697,0,true,161952484800,161952484864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925023922855,0,false,-189997572736,-189997572672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124198652,0,true,162060243776,162060243840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924899056900,0,false,-190146002240,-190146002176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071781543675,0,false,-28085758464,-28085758400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071821189222,0,false,-28045087936,-28045087872⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (7999/8000), zu := 1,
      A := ⟨174498615656,174612566508⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161943076288,161943076352⟩ : DyadicInterval 40),(⟨-189984614848,-189984614784⟩ : DyadicInterval 40),(⟨748221201859,748221221188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11116638⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11116544,11116608⟩ : DyadicInterval 40),(⟨-11116736,-11116672⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174487704921,174612570876⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161952484800,161952484864⟩ : DyadicInterval 40),(⟨-189997572736,-189997572672⟩ : DyadicInterval 40),(⟨748219457150,748219476480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060243776,162060243840⟩ : DyadicInterval 40),(⟨-190146002240,-190146002176⟩ : DyadicInterval 40),(⟨748199465279,748199484608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28085758464,-28045087872⟩ : DyadicInterval 40),(⟨776145927552,776166282112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2226_ok : ecellOkT e2226 = true := by decide +kernel
theorem e2226_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2226 e2226_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '7999/8000', '1']  interval_lower 201944721/1099511627776
noncomputable def e2227 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274102367712,0,true,162041404480,162041404544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924920887840,0,false,-190120050112,-190120050048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522751940,0,true,11124096,11124160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500503612,0,false,-11124224,-11124160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274113276419,0,true,162050818304,162050818368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924909979133,0,false,-190133018048,-190133017984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238149506,0,true,162158573824,162158573888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924785106046,0,false,-190281474304,-190281474240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071745338975,0,false,-28122900480,-28122900416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071785012670,0,false,-28082199680,-28082199616⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (7999/8000), zu := 1,
      A := ⟨174612566507,174726517359⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162041404480,162041404544⟩ : DyadicInterval 40),(⟨-190120050112,-190120050048⟩ : DyadicInterval 40),(⟨748202961613,748202980942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11124164⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11124096,11124160⟩ : DyadicInterval 40),(⟨-11124224,-11124160⟩ : DyadicInterval 40),(⟨762123383503,762123402832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174601648643,174726521730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162050818304,162050818368⟩ : DyadicInterval 40),(⟨-190133018048,-190133017984⟩ : DyadicInterval 40),(⟨748201214596,748201233925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158573824,162158573888⟩ : DyadicInterval 40),(⟨-190281474304,-190281474240⟩ : DyadicInterval 40),(⟨748181208285,748181227615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28122900480,-28082199616⟩ : DyadicInterval 40),(⟨776164483424,776184853120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2227_ok : ecellOkT e2227 = true := by decide +kernel
theorem e2227_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2227 e2227_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '3999/4000', '7999/8000']  interval_lower 203269577/1099511627776
noncomputable def e2228 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274194463504,0,true,162120877504,162120877568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924828792048,0,false,-190229535616,-190229535552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274330240928,0,true,162238034560,162238034624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924693014624,0,false,-190390970688,-190390970624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522751373,0,true,11123520,11123584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500504179,0,false,-11123712,-11123648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533890847,0,true,22262784,22262848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489364705,0,false,-22263360,-22263296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627325,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274216299780,0,true,162139720000,162139720064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924806955772,0,false,-190255496704,-190255496640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274341172839,0,true,162247466752,162247466816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924682082713,0,false,-190403969472,-190403969408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071712585860,0,false,-28156502656,-28156502592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071752282947,0,false,-28115776640,-28115776576⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162120877504,162120877568⟩ : DyadicInterval 40),(⟨-190229535616,-190229535552⟩ : DyadicInterval 40),(⟨748188209004,748188228334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162238034560,162238034624⟩ : DyadicInterval 40),(⟨-190390970688,-190390970624⟩ : DyadicInterval 40),(⟨748166444738,748166464068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11123597,22263071⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11123520,11123584⟩ : DyadicInterval 40),(⟨-11123712,-11123648⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22262784,22262848⟩ : DyadicInterval 40),(⟨-22263360,-22263296⟩ : DyadicInterval 40),(⟨762123383389,762123402718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174704672004,174829545063⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162139720000,162139720064⟩ : DyadicInterval 40),(⟨-190255496704,-190255496640⟩ : DyadicInterval 40),(⟨748184709978,748184729307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162247466752,162247466816⟩ : DyadicInterval 40),(⟨-190403969472,-190403969408⟩ : DyadicInterval 40),(⟨748164691689,748164711018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28156502656,-28115776576⟩ : DyadicInterval 40),(⟨776181271904,776201654208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2228_ok : ecellOkT e2228 = true := by decide +kernel
theorem e2228_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2228 e2228_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '3999/4000', '7999/8000']  interval_lower 204430869/1099511627776
noncomputable def e2229 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274308385867,0,true,162219177536,162219177600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924714869685,0,false,-190364984128,-190364984064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274444177535,0,true,162336336384,162336336448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924579078017,0,false,-190526456064,-190526456000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522758900,0,true,11131008,11131072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500496652,0,false,-11131200,-11131136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533905901,0,true,22277888,22277952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489349651,0,false,-22278400,-22278336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627324,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274330236382,0,true,162238030656,162238030720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924693019170,0,false,-190390965312,-190390965248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274455116564,0,true,162345773888,162345773952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924568138988,0,false,-190539464832,-190539464768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071676338456,0,false,-28193690944,-28193690880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071716063689,0,false,-28152934656,-28152934592⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162219177536,162219177600⟩ : DyadicInterval 40),(⟨-190364984128,-190364984064⟩ : DyadicInterval 40),(⟨748169949128,748169968457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162336336384,162336336448⟩ : DyadicInterval 40),(⟨-190526456064,-190526456000⟩ : DyadicInterval 40),(⟨748148168171,748148187501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11131124,22278125⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11131008,11131072⟩ : DyadicInterval 40),(⟨-11131200,-11131136⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22277888,22277952⟩ : DyadicInterval 40),(⟨-22278400,-22278336⟩ : DyadicInterval 40),(⟨762123383356,762123402685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174818608606,174943488788⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162238030656,162238030720⟩ : DyadicInterval 40),(⟨-190390965312,-190390965248⟩ : DyadicInterval 40),(⟨748166445469,748166464799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162345773888,162345773952⟩ : DyadicInterval 40),(⟨-190539464832,-190539464768⟩ : DyadicInterval 40),(⟨748146412774,748146432104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28193690944,-28152934592⟩ : DyadicInterval 40),(⟨776199850912,776220248352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2229_ok : ecellOkT e2229 = true := by decide +kernel
theorem e2229_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2229 e2229_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '7999/8000', '1']  interval_lower 203102973/1099511627776
noncomputable def e2230 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274216304319,0,true,162139723904,162139723968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924806951233,0,false,-190255502080,-190255502016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522759467,0,true,11131584,11131648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500496085,0,false,-11131776,-11131712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274227220146,0,true,162149143040,162149143104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924796035406,0,false,-190268480064,-190268480000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352100354,0,true,162256895040,162256895104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924671155198,0,false,-190416963072,-190416963008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071709110659,0,false,-28160068032,-28160067968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071748812499,0,false,-28119336960,-28119336896⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (7999/8000), zu := 1,
      A := ⟨174726517358,174840468210⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162139723904,162139723968⟩ : DyadicInterval 40),(⟨-190255502080,-190255502016⟩ : DyadicInterval 40),(⟨748184709249,748184728578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11131691⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11131584,11131648⟩ : DyadicInterval 40),(⟨-11131776,-11131712⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174715592370,174840472578⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162149143040,162149143104⟩ : DyadicInterval 40),(⟨-190268480064,-190268480000⟩ : DyadicInterval 40),(⟨748182959919,748182979249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256895040,162256895104⟩ : DyadicInterval 40),(⟨-190416963072,-190416963008⟩ : DyadicInterval 40),(⟨748162939204,748162958533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28160068032,-28119336896⟩ : DyadicInterval 40),(⟨776183052064,776203436896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2230_ok : ecellOkT e2230 = true := by decide +kernel
theorem e2230_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2230 e2230_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '7999/8000', '1']  interval_lower 204264061/1099511627776
noncomputable def e2231 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274330240926,0,true,162238034560,162238034624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924693014626,0,false,-190390970688,-190390970624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522766994,0,true,11139136,11139200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500488558,0,false,-11139328,-11139264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274341163874,0,true,162247459008,162247459072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924682091678,0,false,-190403958784,-190403958720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466051205,0,true,162355207488,162355207552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924557204347,0,false,-190552468608,-190552468544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071672858722,0,false,-28197261056,-28197260992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071712588712,0,false,-28156499776,-28156499712⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (7999/8000), zu := 1,
      A := ⟨174840468209,174954419061⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162238034560,162238034624⟩ : DyadicInterval 40),(⟨-190390970688,-190390970624⟩ : DyadicInterval 40),(⟨748166444739,748166464068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11139218⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11139136,11139200⟩ : DyadicInterval 40),(⟨-11139328,-11139264⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174829536098,174954423429⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162247459008,162247459072⟩ : DyadicInterval 40),(⟨-190403958784,-190403958720⟩ : DyadicInterval 40),(⟨748164693120,748164712449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355207488,162355207552⟩ : DyadicInterval 40),(⟨-190552468608,-190552468544⟩ : DyadicInterval 40),(⟨748144658022,748144677351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28197261056,-28156499712⟩ : DyadicInterval 40),(⟨776201633472,776222033408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2231_ok : ecellOkT e2231 = true := by decide +kernel
theorem e2231_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2231 e2231_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '999/1000', '7993/8000']  interval_lower 103299061/549755813888
noncomputable def e2232 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274291092416,0,true,162204256128,162204256192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924732163136,0,false,-190344421952,-190344421888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274426812865,0,true,162321355136,162321355200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924596442687,0,false,-190505806144,-190505806080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589598774,0,true,77968192,77968256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433656778,0,false,-77973824,-77973760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600798467,0,true,89167040,89167104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422457085,0,false,-89174336,-89174272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620544,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622247,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274378565834,0,true,162279729216,162279729280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924644689718,0,false,-190448433216,-190448433152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274503410262,0,true,162387437568,162387437632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924519845290,0,false,-190596897984,-190596897920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071660968297,0,false,-28209460416,-28209460352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071700693128,0,false,-28168703936,-28168703872⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162204256128,162204256192⟩ : DyadicInterval 40),(⟨-190344421952,-190344421888⟩ : DyadicInterval 40),(⟨748172721772,748172741102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162321355136,162321355200⟩ : DyadicInterval 40),(⟨-190505806144,-190505806080⟩ : DyadicInterval 40),(⟨748150954412,748150973742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77970998,89170691⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77968192,77968256⟩ : DyadicInterval 40),(⟨-77973824,-77973760⟩ : DyadicInterval 40),(⟨762123380838,762123400167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89167040,89167104⟩ : DyadicInterval 40),(⟨-89174336,-89174272⟩ : DyadicInterval 40),(⟨762123379967,762123399297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174866938058,174991782486⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162279729216,162279729280⟩ : DyadicInterval 40),(⟨-190448433216,-190448433152⟩ : DyadicInterval 40),(⟨748158694426,748158713755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162387437568,162387437632⟩ : DyadicInterval 40),(⟨-190596897984,-190596897920⟩ : DyadicInterval 40),(⟨748138661812,748138681141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28209460416,-28168703872⟩ : DyadicInterval 40),(⟨776207735552,776228133088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2232_ok : ecellOkT e2232 = true := by decide +kernel
theorem e2232_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2232 e2232_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '999/1000', '7993/8000']  interval_lower 103883791/549755813888
noncomputable def e2233 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274404929317,0,true,162302474944,162302475008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924618326235,0,false,-190479782976,-190479782912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274540664009,0,true,162419575808,162419575872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924482591543,0,false,-190641203968,-190641203904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589651463,0,true,78020864,78020928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433604089,0,false,-78026496,-78026432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600858690,0,true,89227264,89227328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422396862,0,false,-89234560,-89234496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620534,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622240,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274492459708,0,true,162377990528,162377990592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924530795844,0,false,-190583874816,-190583874752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274617311260,0,true,162485695360,162485695424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924405944292,0,false,-190732366336,-190732366272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071624700876,0,false,-28246670976,-28246670912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071664453840,0,false,-28205884288,-28205884224⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162302474944,162302475008⟩ : DyadicInterval 40),(⟨-190479782976,-190479782912⟩ : DyadicInterval 40),(⟨748154465344,748154484674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162419575808,162419575872⟩ : DyadicInterval 40),(⟨-190641203968,-190641203904⟩ : DyadicInterval 40),(⟨748132681261,748132700590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78023687,89230914⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78020864,78020928⟩ : DyadicInterval 40),(⟨-78026496,-78026432⟩ : DyadicInterval 40),(⟨762123380831,762123400160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89227264,89227328⟩ : DyadicInterval 40),(⟨-89234560,-89234496⟩ : DyadicInterval 40),(⟨762123379958,762123399287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174980831932,175105683484⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162377990528,162377990592⟩ : DyadicInterval 40),(⟨-190583874816,-190583874752⟩ : DyadicInterval 40),(⟨748140419517,748140438847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162485695360,162485695424⟩ : DyadicInterval 40),(⟨-190732366336,-190732366272⟩ : DyadicInterval 40),(⟨748120372510,748120391839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28246670976,-28205884224⟩ : DyadicInterval 40),(⟨776226325728,776246738368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2233_ok : ecellOkT e2233 = true := by decide +kernel
theorem e2233_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2233 e2233_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '7993/8000', '3997/4000']  interval_lower 6450981/34359738368
noncomputable def e2234 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274312961719,0,true,162223125696,162223125760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924710293833,0,false,-190370424960,-190370424896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274448696411,0,true,162340235008,162340235072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924574559141,0,false,-190531829952,-190531829888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578460180,0,true,66830336,66830400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444795372,0,false,-66834496,-66834432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589652346,0,true,78021760,78021824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433603206,0,false,-78027392,-78027328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622239,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623714,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274389500296,0,true,162289163264,162289163328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924633755256,0,false,-190461435648,-190461435584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274514351870,0,true,162396876800,162396876864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924508903682,0,false,-190609910720,-190609910656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071657485385,0,false,-28213033856,-28213033792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071697214973,0,false,-28172272384,-28172272320⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162223125696,162223125760⟩ : DyadicInterval 40),(⟨-190370424960,-190370424896⟩ : DyadicInterval 40),(⟨748169215452,748169234781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162340235008,162340235072⟩ : DyadicInterval 40),(⟨-190531829952,-190531829888⟩ : DyadicInterval 40),(⟨748147443041,748147462370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66832404,78024570⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66830336,66830400⟩ : DyadicInterval 40),(⟨-66834496,-66834432⟩ : DyadicInterval 40),(⟨762123381569,762123400898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78021760,78021824⟩ : DyadicInterval 40),(⟨-78027392,-78027328⟩ : DyadicInterval 40),(⟨762123380830,762123400160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174877872520,175002724094⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162289163264,162289163328⟩ : DyadicInterval 40),(⟨-190461435648,-190461435584⟩ : DyadicInterval 40),(⟨748156940439,748156959769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162396876800,162396876864⟩ : DyadicInterval 40),(⟨-190609910720,-190609910656⟩ : DyadicInterval 40),(⟨748136905458,748136924788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28213033856,-28172272320⟩ : DyadicInterval 40),(⟨776209519776,776229919808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2234_ok : ecellOkT e2234 = true := by decide +kernel
theorem e2234_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2234 e2234_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '7993/8000', '3997/4000']  interval_lower 207600155/1099511627776
noncomputable def e2235 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274426812863,0,true,162321355136,162321355200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924596442689,0,false,-190505806144,-190505806080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274562561799,0,true,162438466304,162438466368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924460693753,0,false,-190667247936,-190667247872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578505343,0,true,66875520,66875584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444750209,0,false,-66879616,-66879552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589705041,0,true,78074432,78074496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433550511,0,false,-78080064,-78080000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622231,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623709,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274503401292,0,true,162387429824,162387429888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924519854260,0,false,-190596887360,-190596887296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274628259991,0,true,162495139904,162495139968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924394995561,0,false,-190745389120,-190745389056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071621213428,0,false,-28250249216,-28250249152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071660971153,0,false,-28209457472,-28209457408⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162321355136,162321355200⟩ : DyadicInterval 40),(⟨-190505806144,-190505806080⟩ : DyadicInterval 40),(⟨748150954412,748150973742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162438466304,162438466368⟩ : DyadicInterval 40),(⟨-190667247936,-190667247872⟩ : DyadicInterval 40),(⟨748129165270,748129184599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66877567,78077265⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66875520,66875584⟩ : DyadicInterval 40),(⟨-66879616,-66879552⟩ : DyadicInterval 40),(⟨762123381532,762123400861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78074432,78074496⟩ : DyadicInterval 40),(⟨-78080064,-78080000⟩ : DyadicInterval 40),(⟨762123380823,762123400152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174991773516,175116632215⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162387429824,162387429888⟩ : DyadicInterval 40),(⟨-190596887360,-190596887296⟩ : DyadicInterval 40),(⟨748138663274,748138682603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162495139904,162495139968⟩ : DyadicInterval 40),(⟨-190745389120,-190745389056⟩ : DyadicInterval 40),(⟨748118613831,748118633160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28250249216,-28209457408⟩ : DyadicInterval 40),(⟨776228112320,776248527488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2235_ok : ecellOkT e2235 = true := by decide +kernel
theorem e2235_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2235 e2235_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '999/1000', '7993/8000']  interval_lower 104469877/549755813888
noncomputable def e2236 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274518766217,0,true,162400685056,162400685120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924504489335,0,false,-190615160640,-190615160576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274654515153,0,true,162517787712,162517787776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924368740399,0,false,-190776618496,-190776618432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589704158,0,true,78073600,78073664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433551394,0,false,-78079168,-78079104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600918915,0,true,89287488,89287552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422336637,0,false,-89294784,-89294720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620524,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622232,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274606353585,0,true,162476243008,162476243072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924416901967,0,false,-190719333120,-190719333056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274731212259,0,true,162583944320,162583944384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924292043293,0,false,-190867851392,-190867851328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071588409857,0,false,-28283907072,-28283907008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071628190956,0,false,-28243090112,-28243090048⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162400685056,162400685120⟩ : DyadicInterval 40),(⟨-190615160640,-190615160576⟩ : DyadicInterval 40),(⟨748136196774,748136216103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162517787712,162517787776⟩ : DyadicInterval 40),(⟨-190776618496,-190776618432⟩ : DyadicInterval 40),(⟨748114396022,748114415352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78076382,89291139⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78073600,78073664⟩ : DyadicInterval 40),(⟨-78079168,-78079104⟩ : DyadicInterval 40),(⟨762123380791,762123400120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89287488,89287552⟩ : DyadicInterval 40),(⟨-89294784,-89294720⟩ : DyadicInterval 40),(⟨762123379948,762123399277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175094725809,175219584483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162476243008,162476243072⟩ : DyadicInterval 40),(⟨-190719333120,-190719333056⟩ : DyadicInterval 40),(⟨748122132542,748122151871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162583944320,162583944384⟩ : DyadicInterval 40),(⟨-190867851392,-190867851328⟩ : DyadicInterval 40),(⟨748102071136,748102090465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28283907072,-28243090048⟩ : DyadicInterval 40),(⟨776244928640,776265356416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2236_ok : ecellOkT e2236 = true := by decide +kernel
theorem e2236_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2236 e2236_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '999/1000', '7993/8000']  interval_lower 105057299/549755813888
noncomputable def e2237 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274632603117,0,true,162498886336,162498886400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924390652435,0,false,-190750555008,-190750554944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274768366298,0,true,162615990848,162615990912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924254889254,0,false,-190912049728,-190912049664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589756854,0,true,78126272,78126336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433498698,0,false,-78131904,-78131840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600979146,0,true,89347712,89347776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422276406,0,false,-89355008,-89354944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620514,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622225,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274720247459,0,true,162574486656,162574486720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924303008093,0,false,-190854808064,-190854808000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274845113258,0,true,162682184576,162682184640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924178142294,0,false,-191003353152,-191003353088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071552095239,0,false,-28321168576,-28321168512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071591904478,0,false,-28280321344,-28280321280⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162498886336,162498886400⟩ : DyadicInterval 40),(⟨-190750555008,-190750554944⟩ : DyadicInterval 40),(⟨748117916160,748117935490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162615990848,162615990912⟩ : DyadicInterval 40),(⟨-190912049728,-190912049664⟩ : DyadicInterval 40),(⟨748096098696,748096118026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78129078,89351370⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78126272,78126336⟩ : DyadicInterval 40),(⟨-78131904,-78131840⟩ : DyadicInterval 40),(⟨762123380816,762123400145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89347712,89347776⟩ : DyadicInterval 40),(⟨-89355008,-89354944⟩ : DyadicInterval 40),(⟨762123379938,762123399268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175208619683,175333485482⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162574486656,162574486720⟩ : DyadicInterval 40),(⟨-190854808064,-190854808000⟩ : DyadicInterval 40),(⟨748103833472,748103852801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162682184576,162682184640⟩ : DyadicInterval 40),(⟨-191003353152,-191003353088⟩ : DyadicInterval 40),(⟨748083757615,748083776944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28321168576,-28280321280⟩ : DyadicInterval 40),(⟨776263544256,776283987168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2237_ok : ecellOkT e2237 = true := by decide +kernel
theorem e2237_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2237 e2237_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '7993/8000', '3997/4000']  interval_lower 104382119/549755813888
noncomputable def e2238 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274540664007,0,true,162419575808,162419575872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924482591545,0,false,-190641203968,-190641203904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274676427187,0,true,162536688768,162536688832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924346828365,0,false,-190802682560,-190802682496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578550509,0,true,66920640,66920704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444705043,0,false,-66924800,-66924736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589757739,0,true,78127168,78127232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433497813,0,false,-78132800,-78132736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622224,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623703,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274617302288,0,true,162485687616,162485687680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924405953264,0,false,-190732355712,-190732355648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274742172208,0,true,162593397760,162593397824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924281083344,0,false,-190880889152,-190880889088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071584916565,0,false,-28287491392,-28287491328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071624703735,0,false,-28246668032,-28246667968⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162419575808,162419575872⟩ : DyadicInterval 40),(⟨-190641203968,-190641203904⟩ : DyadicInterval 40),(⟨748132681261,748132700590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162536688768,162536688832⟩ : DyadicInterval 40),(⟨-190802682560,-190802682496⟩ : DyadicInterval 40),(⟨748110875416,748110894746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66922733,78129963⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66920640,66920704⟩ : DyadicInterval 40),(⟨-66924800,-66924736⟩ : DyadicInterval 40),(⟨762123381558,762123400887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78127168,78127232⟩ : DyadicInterval 40),(⟨-78132800,-78132736⟩ : DyadicInterval 40),(⟨762123380815,762123400145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175105674512,175230544432⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162485687616,162485687680⟩ : DyadicInterval 40),(⟨-190732355712,-190732355648⟩ : DyadicInterval 40),(⟨748120373973,748120393303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162593397760,162593397824⟩ : DyadicInterval 40),(⟨-190880889152,-190880889088⟩ : DyadicInterval 40),(⟨748100309464,748100328793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28287491392,-28246667968⟩ : DyadicInterval 40),(⟨776246717600,776267148576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2238_ok : ecellOkT e2238 = true := by decide +kernel
theorem e2238_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2238 e2238_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '7993/8000', '3997/4000']  interval_lower 209946533/1099511627776
noncomputable def e2239 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274654515151,0,true,162517787712,162517787776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924368740401,0,false,-190776618496,-190776618432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274790292576,0,true,162634902528,162634902592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924232962976,0,false,-190938133952,-190938133888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578595678,0,true,66965824,66965888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444659874,0,false,-66969984,-66969920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589810441,0,true,78179840,78179904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433445111,0,false,-78185472,-78185408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622216,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623698,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274731203284,0,true,162583936576,162583936640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924292052268,0,false,-190867840768,-190867840704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274856076234,0,true,162691639744,162691639808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924167179318,0,false,-191016396096,-191016396032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071548598710,0,false,-28324756352,-28324756288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071588412718,0,false,-28283904128,-28283904064⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162517787712,162517787776⟩ : DyadicInterval 40),(⟨-190776618496,-190776618432⟩ : DyadicInterval 40),(⟨748114396023,748114415352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162634902528,162634902592⟩ : DyadicInterval 40),(⟨-190938133952,-190938133888⟩ : DyadicInterval 40),(⟨748092573458,748092592787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66967902,78182665⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66965824,66965888⟩ : DyadicInterval 40),(⟨-66969984,-66969920⟩ : DyadicInterval 40),(⟨762123381553,762123400882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78179840,78179904⟩ : DyadicInterval 40),(⟨-78185472,-78185408⟩ : DyadicInterval 40),(⟨762123380808,762123400137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175219575508,175344448458⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162583936576,162583936640⟩ : DyadicInterval 40),(⟨-190867840768,-190867840704⟩ : DyadicInterval 40),(⟨748102072602,748102091931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162691639744,162691639808⟩ : DyadicInterval 40),(⟨-191016396096,-191016396032⟩ : DyadicInterval 40),(⟨748081994303,748082013633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28324756352,-28283904064⟩ : DyadicInterval 40),(⟨776265335648,776285781056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2239_ok : ecellOkT e2239 = true := by decide +kernel
theorem e2239_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2239 e2239_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '3997/4000', '1599/1600']  interval_lower 103132077/549755813888
noncomputable def e2240 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274334831021,0,true,162241994944,162241995008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924688424531,0,false,-190396428608,-190396428544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274470579957,0,true,162359114560,162359114624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924552675595,0,false,-190557854336,-190557854272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567321533,0,true,55692288,55692352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455934019,0,false,-55695168,-55695104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578506172,0,true,66876352,66876416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444749380,0,false,-66880448,-66880384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623708,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624955,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274400434782,0,true,162298597248,162298597312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924622820770,0,false,-190474438272,-190474438208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274525293506,0,true,162406316032,162406316096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924497962046,0,false,-190622923584,-190622923520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071654002246,0,false,-28216607552,-28216607488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071693736593,0,false,-28175841024,-28175840960⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162241994944,162241995008⟩ : DyadicInterval 40),(⟨-190396428608,-190396428544⟩ : DyadicInterval 40),(⟨748165708693,748165728023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162359114560,162359114624⟩ : DyadicInterval 40),(⟨-190557854336,-190557854272⟩ : DyadicInterval 40),(⟨748143931204,748143950533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55693757,66878396⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55692288,55692352⟩ : DyadicInterval 40),(⟨-55695168,-55695104⟩ : DyadicInterval 40),(⟨762123382170,762123401500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66876352,66876416⟩ : DyadicInterval 40),(⟨-66880448,-66880384⟩ : DyadicInterval 40),(⟨762123381531,762123400861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174888807006,175013665730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162298597248,162298597312⟩ : DyadicInterval 40),(⟨-190474438272,-190474438208⟩ : DyadicInterval 40),(⟨748155186344,748155205673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162406316032,162406316096⟩ : DyadicInterval 40),(⟨-190622923584,-190622923520⟩ : DyadicInterval 40),(⟨748135148930,748135168260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28216607552,-28175840960⟩ : DyadicInterval 40),(⟨776211304096,776231706656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2240_ok : ecellOkT e2240 = true := by decide +kernel
theorem e2240_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2240 e2240_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '3997/4000', '1599/1600']  interval_lower 207432693/1099511627776
noncomputable def e2241 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274448696409,0,true,162340235008,162340235072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924574559143,0,false,-190531829952,-190531829888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274584459589,0,true,162457356416,162457356480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924438795963,0,false,-190693292480,-190693292416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567359169,0,true,55729920,55729984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455896383,0,false,-55732864,-55732800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578551340,0,true,66921472,66921536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444704212,0,false,-66925632,-66925568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623702,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624952,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274514342901,0,true,162396869056,162396869120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924508912651,0,false,-190609900032,-190609899968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274639208746,0,true,162504584384,162504584448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924384046806,0,false,-190758412096,-190758412032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071617725754,0,false,-28253827648,-28253827584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071657488241,0,false,-28213030912,-28213030848⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162340235008,162340235072⟩ : DyadicInterval 40),(⟨-190531829952,-190531829888⟩ : DyadicInterval 40),(⟨748147443041,748147462371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162457356416,162457356480⟩ : DyadicInterval 40),(⟨-190693292480,-190693292416⟩ : DyadicInterval 40),(⟨748125648849,748125668178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55731393,66923564⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55729920,55729984⟩ : DyadicInterval 40),(⟨-55732864,-55732800⟩ : DyadicInterval 40),(⟨762123382199,762123401528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66921472,66921536⟩ : DyadicInterval 40),(⟨-66925632,-66925568⟩ : DyadicInterval 40),(⟨762123381558,762123400887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175002715125,175127580970⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162396869056,162396869120⟩ : DyadicInterval 40),(⟨-190609900032,-190609899968⟩ : DyadicInterval 40),(⟨748136906893,748136926223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162504584384,162504584448⟩ : DyadicInterval 40),(⟨-190758412096,-190758412032⟩ : DyadicInterval 40),(⟨748116855042,748116874372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28253827648,-28213030848⟩ : DyadicInterval 40),(⟨776229899040,776250316704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2241_ok : ecellOkT e2241 = true := by decide +kernel
theorem e2241_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2241 e2241_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '1599/1600', '1999/2000']  interval_lower 103048407/549755813888
noncomputable def e2242 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274356700323,0,true,162260863872,162260863936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924666555229,0,false,-190422432896,-190422432832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274492463504,0,true,162377993792,162377993856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924530792048,0,false,-190583879360,-190583879296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556182834,0,true,44554112,44554176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467072718,0,false,-44555968,-44555904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567359947,0,true,55730752,55730816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455895605,0,false,-55733632,-55733568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624951,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625971,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274411369293,0,true,162308031104,162308031168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924611886259,0,false,-190487441088,-190487441024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274536235167,0,true,162415755200,162415755264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924487020385,0,false,-190635936640,-190635936576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071650518881,0,false,-28220181440,-28220181376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071690257988,0,false,-28179409920,-28179409856⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162260863872,162260863936⟩ : DyadicInterval 40),(⟨-190422432896,-190422432832⟩ : DyadicInterval 40),(⟨748162201497,748162220827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162377993792,162377993856⟩ : DyadicInterval 40),(⟨-190583879360,-190583879296⟩ : DyadicInterval 40),(⟨748140418927,748140438256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44555058,55732171⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44554112,44554176⟩ : DyadicInterval 40),(⟨-44555968,-44555904⟩ : DyadicInterval 40),(⟨762123382674,762123402003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55730752,55730816⟩ : DyadicInterval 40),(⟨-55733632,-55733568⟩ : DyadicInterval 40),(⟨762123382166,762123401496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174899741517,175024607391⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162308031104,162308031168⟩ : DyadicInterval 40),(⟨-190487441088,-190487441024⟩ : DyadicInterval 40),(⟨748153432176,748153451506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162415755200,162415755264⟩ : DyadicInterval 40),(⟨-190635936640,-190635936576⟩ : DyadicInterval 40),(⟨748133392293,748133411623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28220181440,-28179409856⟩ : DyadicInterval 40),(⟨776213088544,776233493600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2242_ok : ecellOkT e2242 = true := by decide +kernel
theorem e2242_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2242 e2242_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '1599/1600', '1999/2000']  interval_lower 207265115/1099511627776
noncomputable def e2243 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274470579955,0,true,162359114560,162359114624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924552675597,0,false,-190557854336,-190557854272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274606357379,0,true,162476246272,162476246336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924416898173,0,false,-190719337600,-190719337536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556212944,0,true,44584256,44584320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467042608,0,false,-44586112,-44586048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567397587,0,true,55768384,55768448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455857965,0,false,-55771264,-55771200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624947,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625969,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274525284536,0,true,162406308288,162406308352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924497971016,0,false,-190622912896,-190622912832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274650157531,0,true,162514028864,162514028928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924373098021,0,false,-190771435264,-190771435200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071614237853,0,false,-28257406336,-28257406272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071654005102,0,false,-28216604608,-28216604544⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162359114560,162359114624⟩ : DyadicInterval 40),(⟨-190557854336,-190557854272⟩ : DyadicInterval 40),(⟨748143931204,748143950533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162476246272,162476246336⟩ : DyadicInterval 40),(⟨-190719337600,-190719337536⟩ : DyadicInterval 40),(⟨748122131924,748122151253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44585168,55769811⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44584256,44584320⟩ : DyadicInterval 40),(⟨-44586112,-44586048⟩ : DyadicInterval 40),(⟨762123382672,762123402001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55768384,55768448⟩ : DyadicInterval 40),(⟨-55771264,-55771200⟩ : DyadicInterval 40),(⟨762123382163,762123401492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175013656760,175138529755⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162406308288,162406308352⟩ : DyadicInterval 40),(⟨-190622912896,-190622912832⟩ : DyadicInterval 40),(⟨748135150366,748135169695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162514028864,162514028928⟩ : DyadicInterval 40),(⟨-190771435264,-190771435200⟩ : DyadicInterval 40),(⟨748115096105,748115115435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28257406336,-28216604544⟩ : DyadicInterval 40),(⟨776231685888,776252106048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2243_ok : ecellOkT e2243 = true := by decide +kernel
theorem e2243_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2243 e2243_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '3997/4000', '1599/1600']  interval_lower 208604049/1099511627776
noncomputable def e2244 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274562561797,0,true,162438466304,162438466368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924460693755,0,false,-190667247936,-190667247872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274698339221,0,true,162555589568,162555589632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924324916331,0,false,-190828747264,-190828747200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567396809,0,true,55767616,55767680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455858743,0,false,-55770496,-55770432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578596510,0,true,66966656,66966720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444659042,0,false,-66970816,-66970752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623697,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624948,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274628251018,0,true,162495132160,162495132224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924395004534,0,false,-190745378496,-190745378432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274753123993,0,true,162602844032,162602844096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924270131559,0,false,-190893917312,-190893917248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071581425656,0,false,-28291073280,-28291073216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071621216287,0,false,-28250246272,-28250246208⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162438466304,162438466368⟩ : DyadicInterval 40),(⟨-190667247936,-190667247872⟩ : DyadicInterval 40),(⟨748129165270,748129184600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162555589568,162555589632⟩ : DyadicInterval 40),(⟨-190828747264,-190828747200⟩ : DyadicInterval 40),(⟨748107354331,748107373661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55769033,66968734⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55767616,55767680⟩ : DyadicInterval 40),(⟨-55770496,-55770432⟩ : DyadicInterval 40),(⟨762123382163,762123401492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66966656,66966720⟩ : DyadicInterval 40),(⟨-66970816,-66970752⟩ : DyadicInterval 40),(⟨762123381552,762123400882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175116623242,175241496217⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162495132160,162495132224⟩ : DyadicInterval 40),(⟨-190745378496,-190745378432⟩ : DyadicInterval 40),(⟨748118615295,748118634624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162602844032,162602844096⟩ : DyadicInterval 40),(⟨-190893917312,-190893917248⟩ : DyadicInterval 40),(⟨748098549001,748098568330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28291073280,-28250246208⟩ : DyadicInterval 40),(⟨776248506720,776268939520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2244_ok : ecellOkT e2244 = true := by decide +kernel
theorem e2244_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2244 e2244_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '3997/4000', '1599/1600']  interval_lower 104889211/549755813888
noncomputable def e2245 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274676427185,0,true,162536688768,162536688832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924346828367,0,false,-190802682560,-190802682496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274812218854,0,true,162653813888,162653813952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924211036698,0,false,-190964218816,-190964218752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567434449,0,true,55805248,55805312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455821103,0,false,-55808128,-55808064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578641684,0,true,67011840,67011904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444613868,0,false,-67016000,-67015936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623691,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624944,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274742159137,0,true,162593386496,162593386560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924281096415,0,false,-190880873600,-190880873536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274867039235,0,true,162701094848,162701094912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924156216317,0,false,-191029439232,-191029439168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071545101955,0,false,-28328344384,-28328344320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071584920732,0,false,-28287487104,-28287487040⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162536688768,162536688832⟩ : DyadicInterval 40),(⟨-190802682560,-190802682496⟩ : DyadicInterval 40),(⟨748110875417,748110894746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162653813888,162653813952⟩ : DyadicInterval 40),(⟨-190964218816,-190964218752⟩ : DyadicInterval 40),(⟨748089047777,748089067107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55806673,67013908⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55805248,55805312⟩ : DyadicInterval 40),(⟨-55808128,-55808064⟩ : DyadicInterval 40),(⟨762123382159,762123401488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67011840,67011904⟩ : DyadicInterval 40),(⟨-67016000,-67015936⟩ : DyadicInterval 40),(⟨762123381547,762123400876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175230531361,175355411459⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162593386496,162593386560⟩ : DyadicInterval 40),(⟨-190880873600,-190880873536⟩ : DyadicInterval 40),(⟨748100311558,748100330887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162701094848,162701094912⟩ : DyadicInterval 40),(⟨-191029439232,-191029439168⟩ : DyadicInterval 40),(⟨748080230881,748080250210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28328344384,-28287487040⟩ : DyadicInterval 40),(⟨776267127136,776287575072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2245_ok : ecellOkT e2245 = true := by decide +kernel
theorem e2245_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2245 e2245_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '1599/1600', '1999/2000']  interval_lower 208435913/1099511627776
noncomputable def e2246 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274584459587,0,true,162457356416,162457356480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924438795965,0,false,-190693292480,-190693292416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274720251255,0,true,162574489984,162574490048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924303004297,0,false,-190854812608,-190854812544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556243056,0,true,44614336,44614400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467012496,0,false,-44616192,-44616128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567435228,0,true,55806016,55806080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455820324,0,false,-55808896,-55808832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624943,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625966,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274639199773,0,true,162504576640,162504576704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924384055779,0,false,-190758401408,-190758401344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274764079895,0,true,162612293760,162612293824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924259175657,0,false,-190906950528,-190906950464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071577933217,0,false,-28294656768,-28294656704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071617728614,0,false,-28253824704,-28253824640⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162457356416,162457356480⟩ : DyadicInterval 40),(⟨-190693292480,-190693292416⟩ : DyadicInterval 40),(⟨748125648849,748125668179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162574489984,162574490048⟩ : DyadicInterval 40),(⟨-190854812608,-190854812544⟩ : DyadicInterval 40),(⟨748103832842,748103852171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44615280,55807452⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44614336,44614400⟩ : DyadicInterval 40),(⟨-44616192,-44616128⟩ : DyadicInterval 40),(⟨762123382669,762123401998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55806016,55806080⟩ : DyadicInterval 40),(⟨-55808896,-55808832⟩ : DyadicInterval 40),(⟨762123382159,762123401488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175127571997,175252452119⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162504576640,162504576704⟩ : DyadicInterval 40),(⟨-190758401408,-190758401344⟩ : DyadicInterval 40),(⟨748116856479,748116875809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162612293760,162612293824⟩ : DyadicInterval 40),(⟨-190906950528,-190906950464⟩ : DyadicInterval 40),(⟨748096787773,748096807102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28294656768,-28253824640⟩ : DyadicInterval 40),(⟨776250295936,776270731264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2246_ok : ecellOkT e2246 = true := by decide +kernel
theorem e2246_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2246 e2246_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '1599/1600', '1999/2000']  interval_lower 209609973/1099511627776
noncomputable def e2247 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274698339219,0,true,162555589568,162555589632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924324916333,0,false,-190828747264,-190828747200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274834145131,0,true,162672724864,162672724928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924189110421,0,false,-190990304256,-190990304192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556273168,0,true,44644480,44644544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466982384,0,false,-44646336,-44646272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567472874,0,true,55843648,55843712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455782678,0,false,-55846528,-55846464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624939,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625964,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274753115018,0,true,162602836288,162602836352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924270140534,0,false,-190893906624,-190893906560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274878002259,0,true,162710549888,162710549952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924145253293,0,false,-191042482496,-191042482432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071541604974,0,false,-28331932608,-28331932544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071581428518,0,false,-28291070336,-28291070272⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162555589568,162555589632⟩ : DyadicInterval 40),(⟨-190828747264,-190828747200⟩ : DyadicInterval 40),(⟨748107354332,748107373661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162672724864,162672724928⟩ : DyadicInterval 40),(⟨-190990304256,-190990304192⟩ : DyadicInterval 40),(⟨748085521664,748085540993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44645392,55845098⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44644480,44644544⟩ : DyadicInterval 40),(⟨-44646336,-44646272⟩ : DyadicInterval 40),(⟨762123382667,762123401996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55843648,55843712⟩ : DyadicInterval 40),(⟨-55846528,-55846464⟩ : DyadicInterval 40),(⟨762123382155,762123401484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175241487242,175366374483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162602836288,162602836352⟩ : DyadicInterval 40),(⟨-190893906624,-190893906560⟩ : DyadicInterval 40),(⟨748098550440,748098569770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162710549888,162710549952⟩ : DyadicInterval 40),(⟨-191042482496,-191042482432⟩ : DyadicInterval 40),(⟨748078467321,748078486651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28331932608,-28291070272⟩ : DyadicInterval 40),(⟨776268918752,776289369184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2247_ok : ecellOkT e2247 = true := by decide +kernel
theorem e2247_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2247 e2247_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '999/1000', '7993/8000']  interval_lower 105642477/549755813888
noncomputable def e2248 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274746440018,0,true,162597078848,162597078912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924276815534,0,false,-190885966080,-190885966016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274882217442,0,true,162714185216,162714185280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924141038110,0,false,-191047497600,-191047497536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589809556,0,true,78178944,78179008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433445996,0,false,-78184576,-78184512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601039381,0,true,89407936,89408000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422216171,0,false,-89415296,-89415232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620505,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622217,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274834141333,0,true,162672721600,162672721664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924189114219,0,false,-190990299776,-190990299712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274959018350,0,true,162780419520,162780419584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924064237202,0,false,-191138876480,-191138876416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071515755716,0,false,-28358456896,-28358456832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071555594404,0,false,-28317578112,-28317578048⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162597078848,162597078912⟩ : DyadicInterval 40),(⟨-190885966080,-190885966016⟩ : DyadicInterval 40),(⟨748099623465,748099642794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162714185216,162714185280⟩ : DyadicInterval 40),(⟨-191047497600,-191047497536⟩ : DyadicInterval 40),(⟨748077789254,748077808584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78181780,89411605⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78178944,78179008⟩ : DyadicInterval 40),(⟨-78184576,-78184512⟩ : DyadicInterval 40),(⟨762123380808,762123400138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89407936,89408000⟩ : DyadicInterval 40),(⟨-89415296,-89415232⟩ : DyadicInterval 40),(⟨762123379960,762123399290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175322513557,175447390574⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162672721600,162672721664⟩ : DyadicInterval 40),(⟨-190990299776,-190990299712⟩ : DyadicInterval 40),(⟨748085522284,748085541614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162780419520,162780419584⟩ : DyadicInterval 40),(⟨-191138876480,-191138876416⟩ : DyadicInterval 40),(⟨748065431365,748065450694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28358456896,-28317578048⟩ : DyadicInterval 40),(⟨776282172640,776302631328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2248_ok : ecellOkT e2248 = true := by decide +kernel
theorem e2248_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2248 e2248_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '999/1000', '7993/8000']  interval_lower 106232875/549755813888
noncomputable def e2249 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274860276918,0,true,162695262656,162695262720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924162978634,0,false,-191021393792,-191021393728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274996068586,0,true,162812370816,162812370880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924027186966,0,false,-191182962176,-191182962112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589862261,0,true,78231680,78231744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433393291,0,false,-78237312,-78237248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601099621,0,true,89468160,89468224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422155931,0,false,-89475520,-89475456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620495,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622210,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274948035206,0,true,162770947776,162770947840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924075220346,0,false,-191125808128,-191125808064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275072919354,0,true,162878642240,162878642304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923950336198,0,false,-191274411648,-191274411584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071479393898,0,false,-28395769408,-28395769344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071519260734,0,false,-28354860352,-28354860288⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162695262656,162695262720⟩ : DyadicInterval 40),(⟨-191021393792,-191021393728⟩ : DyadicInterval 40),(⟨748081318623,748081337953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162812370816,162812370880⟩ : DyadicInterval 40),(⟨-191182962176,-191182962112⟩ : DyadicInterval 40),(⟨748059467722,748059487052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78234485,89471845⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78231680,78231744⟩ : DyadicInterval 40),(⟨-78237312,-78237248⟩ : DyadicInterval 40),(⟨762123380801,762123400130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89468160,89468224⟩ : DyadicInterval 40),(⟨-89475520,-89475456⟩ : DyadicInterval 40),(⟨762123379951,762123399280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175436407430,175561291578⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162770947776,162770947840⟩ : DyadicInterval 40),(⟨-191125808128,-191125808064⟩ : DyadicInterval 40),(⟨748067198962,748067218292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162878642240,162878642304⟩ : DyadicInterval 40),(⟨-191274411648,-191274411584⟩ : DyadicInterval 40),(⟨748047093619,748047112949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28395769408,-28354860288⟩ : DyadicInterval 40),(⟨776300813760,776321287584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2249_ok : ecellOkT e2249 = true := by decide +kernel
theorem e2249_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2249 e2249_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '7993/8000', '3997/4000']  interval_lower 211124195/1099511627776
noncomputable def e2250 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274768366296,0,true,162615990848,162615990912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924254889256,0,false,-190912049728,-190912049664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274904157964,0,true,162733107456,162733107520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924119097588,0,false,-191073601984,-191073601920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578640851,0,true,67011008,67011072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444614701,0,false,-67015168,-67015104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589863147,0,true,78232576,78232640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433392405,0,false,-78238208,-78238144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622209,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623692,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274845104280,0,true,162682176832,162682176896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924178151272,0,false,-191003342464,-191003342400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274969984350,0,true,162789876480,162789876544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924053271202,0,false,-191151924608,-191151924544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071512255951,0,false,-28362048128,-28362048064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071552098103,0,false,-28321165632,-28321165568⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162615990848,162615990912⟩ : DyadicInterval 40),(⟨-190912049728,-190912049664⟩ : DyadicInterval 40),(⟨748096098696,748096118026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162733107456,162733107520⟩ : DyadicInterval 40),(⟨-191073601984,-191073601920⟩ : DyadicInterval 40),(⟨748074259415,748074278745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67013075,78235371⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67011008,67011072⟩ : DyadicInterval 40),(⟨-67015168,-67015104⟩ : DyadicInterval 40),(⟨762123381547,762123400876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78232576,78232640⟩ : DyadicInterval 40),(⟨-78238208,-78238144⟩ : DyadicInterval 40),(⟨762123380800,762123400130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175333476504,175458356574⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162682176832,162682176896⟩ : DyadicInterval 40),(⟨-191003342464,-191003342400⟩ : DyadicInterval 40),(⟨748083759057,748083778386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162789876480,162789876544⟩ : DyadicInterval 40),(⟨-191151924608,-191151924544⟩ : DyadicInterval 40),(⟨748063666375,748063685704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28362048128,-28321165568⟩ : DyadicInterval 40),(⟨776283966400,776304426944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2250_ok : ecellOkT e2250 = true := by decide +kernel
theorem e2250_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2250 e2250_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '7993/8000', '3997/4000']  interval_lower 13268529/68719476736
noncomputable def e2251 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274882217440,0,true,162714185216,162714185280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924141038112,0,false,-191047497600,-191047497536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275018023352,0,true,162831303680,162831303744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924005232200,0,false,-191209086720,-191209086656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578686027,0,true,67056192,67056256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444569525,0,false,-67060352,-67060288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589915857,0,true,78285248,78285312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433339695,0,false,-78290880,-78290816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622201,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623687,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274959005274,0,true,162780408256,162780408320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924064250278,0,false,-191138860928,-191138860864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275083896573,0,true,162888107968,162888108032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923939358979,0,false,-191287474752,-191287474688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071475888278,0,false,-28399366720,-28399366656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071515759890,0,false,-28358452608,-28358452544⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162714185216,162714185280⟩ : DyadicInterval 40),(⟨-191047497600,-191047497536⟩ : DyadicInterval 40),(⟨748077789255,748077808584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162831303680,162831303744⟩ : DyadicInterval 40),(⟨-191209086720,-191209086656⟩ : DyadicInterval 40),(⟨748055933238,748055952568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67058251,78288081⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67056192,67056256⟩ : DyadicInterval 40),(⟨-67060352,-67060288⟩ : DyadicInterval 40),(⟨762123381542,762123400871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78285248,78285312⟩ : DyadicInterval 40),(⟨-78290880,-78290816⟩ : DyadicInterval 40),(⟨762123380793,762123400122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175447377498,175572268797⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162780408256,162780408320⟩ : DyadicInterval 40),(⟨-191138860928,-191138860864⟩ : DyadicInterval 40),(⟨748065433465,748065452794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162888107968,162888108032⟩ : DyadicInterval 40),(⟨-191287474752,-191287474688⟩ : DyadicInterval 40),(⟨748045325699,748045345029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28399366720,-28358452544⟩ : DyadicInterval 40),(⟨776302609888,776323086240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2251_ok : ecellOkT e2251 = true := by decide +kernel
theorem e2251_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2251 e2251_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '999/1000', '7993/8000']  interval_lower 53412309/274877906944
noncomputable def e2252 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274974113818,0,true,162793437632,162793437696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924049141734,0,false,-191156838208,-191156838144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275109919730,0,true,162910547648,162910547712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923913335822,0,false,-191318443392,-191318443328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589914971,0,true,78284352,78284416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433340581,0,false,-78289984,-78289920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601159864,0,true,89528384,89528448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422095688,0,false,-89535744,-89535680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620485,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622202,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275061929083,0,true,162869165120,162869165184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923961326469,0,false,-191261333184,-191261333120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275186820352,0,true,162976856128,162976856192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923836435200,0,false,-191409963520,-191409963456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071443008484,0,false,-28433107392,-28433107328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071482903468,0,false,-28392168000,-28392167936⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162793437632,162793437696⟩ : DyadicInterval 40),(⟨-191156838208,-191156838144⟩ : DyadicInterval 40),(⟨748063001734,748063021064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162910547648,162910547712⟩ : DyadicInterval 40),(⟨-191318443392,-191318443328⟩ : DyadicInterval 40),(⟨748041134072,748041153401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78287195,89532088⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78284352,78284416⟩ : DyadicInterval 40),(⟨-78289984,-78289920⟩ : DyadicInterval 40),(⟨762123380793,762123400123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89528384,89528448⟩ : DyadicInterval 40),(⟨-89535744,-89535680⟩ : DyadicInterval 40),(⟨762123379941,762123399270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175550301307,175675192576⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162869165120,162869165184⟩ : DyadicInterval 40),(⟨-191261333184,-191261333120⟩ : DyadicInterval 40),(⟨748048863568,748048882897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162976856128,162976856192⟩ : DyadicInterval 40),(⟨-191409963520,-191409963456⟩ : DyadicInterval 40),(⟨748028743798,748028763127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28433107392,-28392167936⟩ : DyadicInterval 40),(⟨776319467584,776339956576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2252_ok : ecellOkT e2252 = true := by decide +kernel
theorem e2252_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2252 e2252_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '999/1000', '7993/8000']  interval_lower 53708877/274877906944
noncomputable def e2253 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275087950718,0,true,162891603904,162891603968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923935304834,0,false,-191292299328,-191292299264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275223770874,0,true,163008715712,163008715776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923799484678,0,false,-191453941376,-191453941312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589967683,0,true,78337088,78337152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433287869,0,false,-78342720,-78342656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601220112,0,true,89588672,89588736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422035440,0,false,-89596032,-89595968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620475,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622195,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275175822956,0,true,162967373696,162967373760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923847432596,0,false,-191396874944,-191396874880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275300721351,0,true,163075061248,163075061312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923722534201,0,false,-191545532096,-191545532032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071406599471,0,false,-28470470848,-28470470784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071446522607,0,false,-28429501184,-28429501120⟩
    { al := (261891/1638400), au := (40947/256000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162891603904,162891603968⟩ : DyadicInterval 40),(⟨-191292299328,-191292299264⟩ : DyadicInterval 40),(⟨748044672723,748044692053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163008715712,163008715776⟩ : DyadicInterval 40),(⟨-191453941376,-191453941312⟩ : DyadicInterval 40),(⟨748022788356,748022807685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78339907,89592336⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78337088,78337152⟩ : DyadicInterval 40),(⟨-78342720,-78342656⟩ : DyadicInterval 40),(⟨762123380786,762123400115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89588672,89588736⟩ : DyadicInterval 40),(⟨-89596032,-89595968⟩ : DyadicInterval 40),(⟨762123379931,762123399260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175664195180,175789093575⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162967373696,162967373760⟩ : DyadicInterval 40),(⟨-191396874944,-191396874880⟩ : DyadicInterval 40),(⟨748030516063,748030535393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163075061248,163075061312⟩ : DyadicInterval 40),(⟨-191545532096,-191545532032⟩ : DyadicInterval 40),(⟨748010381862,748010401191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28470470848,-28429501120⟩ : DyadicInterval 40),(⟨776338134176,776358638304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2253_ok : ecellOkT e2253 = true := by decide +kernel
theorem e2253_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2253 e2253_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '7993/8000', '3997/4000']  interval_lower 53369925/274877906944
noncomputable def e2254 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274996068584,0,true,162812370816,162812370880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924027186968,0,false,-191182962176,-191182962112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275131888739,0,true,162929491072,162929491136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923891366813,0,false,-191344588160,-191344588096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578731207,0,true,67101376,67101440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444524345,0,false,-67105536,-67105472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589968570,0,true,78337984,78338048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433286982,0,false,-78343616,-78343552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622194,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623681,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275072906275,0,true,162878630912,162878630976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923950349277,0,false,-191274396096,-191274396032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275197804688,0,true,162986327168,162986327232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923825450864,0,false,-191423036672,-191423036608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071439498315,0,false,-28436709504,-28436709440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071479398076,0,false,-28395765120,-28395765056⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162812370816,162812370880⟩ : DyadicInterval 40),(⟨-191182962176,-191182962112⟩ : DyadicInterval 40),(⟨748059467722,748059487052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162929491072,162929491136⟩ : DyadicInterval 40),(⟨-191344588160,-191344588096⟩ : DyadicInterval 40),(⟨748037595001,748037614330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67103431,78340794⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67101376,67101440⟩ : DyadicInterval 40),(⟨-67105536,-67105472⟩ : DyadicInterval 40),(⟨762123381536,762123400865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78337984,78338048⟩ : DyadicInterval 40),(⟨-78343616,-78343552⟩ : DyadicInterval 40),(⟨762123380785,762123400115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175561278499,175686176912⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162878630912,162878630976⟩ : DyadicInterval 40),(⟨-191274396096,-191274396032⟩ : DyadicInterval 40),(⟨748047095759,748047115089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162986327168,162986327232⟩ : DyadicInterval 40),(⟨-191423036672,-191423036608⟩ : DyadicInterval 40),(⟨748026973538,748026992867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28436709504,-28395765056⟩ : DyadicInterval 40),(⟨776321266144,776341757632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2254_ok : ecellOkT e2254 = true := by decide +kernel
theorem e2254_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2254 e2254_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '7993/8000', '3997/4000']  interval_lower 53666477/274877906944
noncomputable def e2255 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275109919728,0,true,162910547648,162910547712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923913335824,0,false,-191318443392,-191318443328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275245754127,0,true,163027669760,163027669824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923777501425,0,false,-191480106304,-191480106240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578776391,0,true,67146560,67146624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444479161,0,false,-67150720,-67150656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590021288,0,true,78390656,78390720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433234264,0,false,-78396352,-78396288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622186,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623676,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275186807270,0,true,162976844800,162976844864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923836448282,0,false,-191409947968,-191409947904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275311712812,0,true,163084537600,163084537664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923711542740,0,false,-191558615360,-191558615296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071403084748,0,false,-28474077760,-28474077696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071443012665,0,false,-28433103104,-28433103040⟩
    { al := (261891/1638400), au := (40947/256000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162910547648,162910547712⟩ : DyadicInterval 40),(⟨-191318443392,-191318443328⟩ : DyadicInterval 40),(⟨748041134072,748041153402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163027669760,163027669824⟩ : DyadicInterval 40),(⟨-191480106304,-191480106240⟩ : DyadicInterval 40),(⟨748019244628,748019263957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67148615,78393512⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67146560,67146624⟩ : DyadicInterval 40),(⟨-67150720,-67150656⟩ : DyadicInterval 40),(⟨762123381531,762123400860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78390656,78390720⟩ : DyadicInterval 40),(⟨-78396352,-78396288⟩ : DyadicInterval 40),(⟨762123380810,762123400139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175675179494,175800085036⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162976844800,162976844864⟩ : DyadicInterval 40),(⟨-191409947968,-191409947904⟩ : DyadicInterval 40),(⟨748028745941,748028765271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163084537600,163084537664⟩ : DyadicInterval 40),(⟨-191558615360,-191558615296⟩ : DyadicInterval 40),(⟨748008609284,748008628614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28474077760,-28433103040⟩ : DyadicInterval 40),(⟨776339935136,776360441760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2255_ok : ecellOkT e2255 = true := by decide +kernel
theorem e2255_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2255 e2255_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '3997/4000', '1599/1600']  interval_lower 52738883/274877906944
noncomputable def e2256 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274790292574,0,true,162634902528,162634902592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924232962978,0,false,-190938133952,-190938133888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274926098485,0,true,162752029440,162752029504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924097157067,0,false,-191099707008,-191099706944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567472094,0,true,55842880,55842944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455783458,0,false,-55845760,-55845696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578686861,0,true,67057024,67057088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444568691,0,false,-67061184,-67061120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623686,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624940,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274856067257,0,true,162691632000,162691632064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924167188295,0,false,-191016385408,-191016385344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274980954474,0,true,162799336896,162799336960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924042301078,0,false,-191164977856,-191164977792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071508754651,0,false,-28365640960,-28365640896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071548601574,0,false,-28324753408,-28324753344⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162634902528,162634902592⟩ : DyadicInterval 40),(⟨-190938133952,-190938133888⟩ : DyadicInterval 40),(⟨748092573458,748092592788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162752029440,162752029504⟩ : DyadicInterval 40),(⟨-191099707008,-191099706944⟩ : DyadicInterval 40),(⟨748070729095,748070748425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55844318,67059085⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55842880,55842944⟩ : DyadicInterval 40),(⟨-55845760,-55845696⟩ : DyadicInterval 40),(⟨762123382155,762123401484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67057024,67057088⟩ : DyadicInterval 40),(⟨-67061184,-67061120⟩ : DyadicInterval 40),(⟨762123381541,762123400871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175344439481,175469326698⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162691632000,162691632064⟩ : DyadicInterval 40),(⟨-191016385408,-191016385344⟩ : DyadicInterval 40),(⟨748081995745,748082015075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162799336896,162799336960⟩ : DyadicInterval 40),(⟨-191164977856,-191164977792⟩ : DyadicInterval 40),(⟨748061900644,748061919974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28365640960,-28324753344⟩ : DyadicInterval 40),(⟨776285760288,776306223360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2256_ok : ecellOkT e2256 = true := by decide +kernel
theorem e2256_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2256 e2256_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '3997/4000', '1599/1600']  interval_lower 106063763/549755813888
noncomputable def e2257 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274904157961,0,true,162733107456,162733107520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924119097591,0,false,-191073601984,-191073601920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275039978117,0,true,162850236224,162850236288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923983277435,0,false,-191235211904,-191235211840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567509742,0,true,55880512,55880576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455745810,0,false,-55883392,-55883328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578732041,0,true,67102208,67102272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444523511,0,false,-67106368,-67106304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623680,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624936,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274969975368,0,true,162789868736,162789868800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924053280184,0,false,-191151913920,-191151913856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275094873817,0,true,162897573696,162897573760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923928381735,0,false,-191300538048,-191300537984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071472382431,0,false,-28402964352,-28402964288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071512258818,0,false,-28362045184,-28362045120⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162733107456,162733107520⟩ : DyadicInterval 40),(⟨-191073601984,-191073601920⟩ : DyadicInterval 40),(⟨748074259416,748074278745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162850236224,162850236288⟩ : DyadicInterval 40),(⟨-191235211904,-191235211840⟩ : DyadicInterval 40),(⟨748052398309,748052417639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55881966,67104265⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55880512,55880576⟩ : DyadicInterval 40),(⟨-55883392,-55883328⟩ : DyadicInterval 40),(⟨762123382151,762123401480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67102208,67102272⟩ : DyadicInterval 40),(⟨-67106368,-67106304⟩ : DyadicInterval 40),(⟨762123381536,762123400865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175458347592,175583246041⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162789868736,162789868800⟩ : DyadicInterval 40),(⟨-191151913920,-191151913856⟩ : DyadicInterval 40),(⟨748063667819,748063687149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162897573696,162897573760⟩ : DyadicInterval 40),(⟨-191300538048,-191300537984⟩ : DyadicInterval 40),(⟨748043557631,748043576960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28402964352,-28362045120⟩ : DyadicInterval 40),(⟨776304406176,776324885056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2257_ok : ecellOkT e2257 = true := by decide +kernel
theorem e2257_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2257 e2257_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '1599/1600', '1999/2000']  interval_lower 210779093/1099511627776
noncomputable def e2258 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274812218851,0,true,162653813888,162653813952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924211036701,0,false,-190964218816,-190964218752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274948039007,0,true,162770951040,162770951104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924075216545,0,false,-191125812608,-191125812544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556303285,0,true,44674560,44674624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466952267,0,false,-44676480,-44676416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567510522,0,true,55881280,55881344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455745030,0,false,-55884224,-55884160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624935,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625961,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274867030257,0,true,162701087104,162701087168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924156225295,0,false,-191029428544,-191029428480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274991928717,0,true,162808800768,162808800832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924031326835,0,false,-191178036096,-191178036032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071505251817,0,false,-28369235328,-28369235264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071545104820,0,false,-28328341440,-28328341376⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162653813888,162653813952⟩ : DyadicInterval 40),(⟨-190964218816,-190964218752⟩ : DyadicInterval 40),(⟨748089047777,748089067107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162770951040,162770951104⟩ : DyadicInterval 40),(⟨-191125812608,-191125812544⟩ : DyadicInterval 40),(⟨748067198340,748067217670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44675509,55882746⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44674560,44674624⟩ : DyadicInterval 40),(⟨-44676480,-44676416⟩ : DyadicInterval 40),(⟨762123382696,762123402025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55881280,55881344⟩ : DyadicInterval 40),(⟨-55884224,-55884160⟩ : DyadicInterval 40),(⟨762123382183,762123401512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175355402481,175480300941⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162701087104,162701087168⟩ : DyadicInterval 40),(⟨-191029428544,-191029428480⟩ : DyadicInterval 40),(⟨748080232323,748080251652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162808800768,162808800832⟩ : DyadicInterval 40),(⟨-191178036096,-191178036032⟩ : DyadicInterval 40),(⟨748060134120,748060153449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28369235328,-28328341376⟩ : DyadicInterval 40),(⟨776287554304,776308020544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2258_ok : ecellOkT e2258 = true := by decide +kernel
theorem e2258_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2258 e2258_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '1599/1600', '1999/2000']  interval_lower 211958609/1099511627776
noncomputable def e2259 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274926098483,0,true,162752029440,162752029504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924097157069,0,false,-191099707008,-191099706944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275061932883,0,true,162869168384,162869168448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923961322669,0,false,-191261337728,-191261337664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556333403,0,true,44704704,44704768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466922149,0,false,-44706560,-44706496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567548171,0,true,55918912,55918976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455707381,0,false,-55921856,-55921792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624931,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625959,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274980945492,0,true,162799329152,162799329216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924042310060,0,false,-191164967168,-191164967104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275105851082,0,true,162907039296,162907039360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923917404470,0,false,-191313601472,-191313601408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071468876358,0,false,-28406562176,-28406562112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071508757519,0,false,-28365638016,-28365637952⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162752029440,162752029504⟩ : DyadicInterval 40),(⟨-191099707008,-191099706944⟩ : DyadicInterval 40),(⟨748070729095,748070748425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162869168384,162869168448⟩ : DyadicInterval 40),(⟨-191261337728,-191261337664⟩ : DyadicInterval 40),(⟨748048862972,748048882302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44705627,55920395⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44704704,44704768⟩ : DyadicInterval 40),(⟨-44706560,-44706496⟩ : DyadicInterval 40),(⟨762123382662,762123401991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55918912,55918976⟩ : DyadicInterval 40),(⟨-55921856,-55921792⟩ : DyadicInterval 40),(⟨762123382179,762123401509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175469317716,175594223306⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162799329152,162799329216⟩ : DyadicInterval 40),(⟨-191164967168,-191164967104⟩ : DyadicInterval 40),(⟨748061902089,748061921418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162907039296,162907039360⟩ : DyadicInterval 40),(⟨-191313601472,-191313601408⟩ : DyadicInterval 40),(⟨748041789462,748041808792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28406562176,-28365637952⟩ : DyadicInterval 40),(⟨776306202592,776326683968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2259_ok : ecellOkT e2259 = true := by decide +kernel
theorem e2259_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2259 e2259_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '3997/4000', '1599/1600']  interval_lower 213310285/1099511627776
noncomputable def e2260 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275018023349,0,true,162831303680,162831303744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924005232203,0,false,-191209086720,-191209086656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275153857749,0,true,162948434240,162948434304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923869397803,0,false,-191370733504,-191370733440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567547391,0,true,55918144,55918208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455708161,0,false,-55921088,-55921024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578777225,0,true,67147392,67147456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444478327,0,false,-67151552,-67151488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623675,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624933,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275083883494,0,true,162888096704,162888096768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923939372058,0,false,-191287459200,-191287459136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275208789056,0,true,162995798144,162995798208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923814466496,0,false,-191436110080,-191436110016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071435987917,0,false,-28440311872,-28440311808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071475892456,0,false,-28399362432,-28399362368⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162831303680,162831303744⟩ : DyadicInterval 40),(⟨-191209086720,-191209086656⟩ : DyadicInterval 40),(⟨748055933239,748055952568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162948434240,162948434304⟩ : DyadicInterval 40),(⟨-191370733504,-191370733440⟩ : DyadicInterval 40),(⟨748034055420,748034074749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55919615,67149449⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55918144,55918208⟩ : DyadicInterval 40),(⟨-55921088,-55921024⟩ : DyadicInterval 40),(⟨762123382179,762123401509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67147392,67147456⟩ : DyadicInterval 40),(⟨-67151552,-67151488⟩ : DyadicInterval 40),(⟨762123381530,762123400860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175572255718,175697161280⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162888096704,162888096768⟩ : DyadicInterval 40),(⟨-191287459200,-191287459136⟩ : DyadicInterval 40),(⟨748045327803,748045347132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162995798144,162995798208⟩ : DyadicInterval 40),(⟨-191436110080,-191436110016⟩ : DyadicInterval 40),(⟨748025203192,748025222522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28440311872,-28399362368⟩ : DyadicInterval 40),(⟨776323064800,776343558816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2260_ok : ecellOkT e2260 = true := by decide +kernel
theorem e2260_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2260 e2260_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '3997/4000', '1599/1600']  interval_lower 107248025/549755813888
noncomputable def e2261 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275131888737,0,true,162929491072,162929491136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923891366815,0,false,-191344588160,-191344588096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275267737380,0,true,163046623424,163046623488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923755518172,0,false,-191506271808,-191506271744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567585044,0,true,55955840,55955904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455670508,0,false,-55958720,-55958656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578822411,0,true,67192576,67192640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444433141,0,false,-67196736,-67196672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623669,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624929,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275197791606,0,true,162986315904,162986315968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923825463946,0,false,-191423021120,-191423021056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275322704297,0,true,163094013888,163094013952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923700551255,0,false,-191571698816,-191571698752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071399569798,0,false,-28477684928,-28477684864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071439502497,0,false,-28436705216,-28436705152⟩
    { al := (261891/1638400), au := (40947/256000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162929491072,162929491136⟩ : DyadicInterval 40),(⟨-191344588160,-191344588096⟩ : DyadicInterval 40),(⟨748037595001,748037614331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163046623424,163046623488⟩ : DyadicInterval 40),(⟨-191506271808,-191506271744⟩ : DyadicInterval 40),(⟨748015700462,748015719792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55957268,67194635⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55955840,55955904⟩ : DyadicInterval 40),(⟨-55958720,-55958656⟩ : DyadicInterval 40),(⟨762123382144,762123401473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67192576,67192640⟩ : DyadicInterval 40),(⟨-67196736,-67196672⟩ : DyadicInterval 40),(⟨762123381525,762123400854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175686163830,175811076521⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162986315904,162986315968⟩ : DyadicInterval 40),(⟨-191423021120,-191423021056⟩ : DyadicInterval 40),(⟨748026975644,748026994974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163094013888,163094013952⟩ : DyadicInterval 40),(⟨-191571698816,-191571698752⟩ : DyadicInterval 40),(⟨748006836595,748006855925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28477684928,-28436705152⟩ : DyadicInterval 40),(⟨776341736192,776362245344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2261_ok : ecellOkT e2261 = true := by decide +kernel
theorem e2261_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2261 e2261_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '1599/1600', '1999/2000']  interval_lower 213140767/1099511627776
noncomputable def e2262 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275039978115,0,true,162850236224,162850236288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923983277437,0,false,-191235211904,-191235211840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275175826758,0,true,162967377024,162967377088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923847428794,0,false,-191396879488,-191396879424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556363522,0,true,44734784,44734848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466892030,0,false,-44736704,-44736640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567585825,0,true,55956608,55956672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455669727,0,false,-55959488,-55959424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624928,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625956,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275094860738,0,true,162897562368,162897562432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923928394814,0,false,-191300522496,-191300522432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275219773446,0,true,163005269056,163005269120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923803482106,0,false,-191449183616,-191449183552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071432477292,0,false,-28443914496,-28443914432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071472386609,0,false,-28402960064,-28402960000⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162850236224,162850236288⟩ : DyadicInterval 40),(⟨-191235211904,-191235211840⟩ : DyadicInterval 40),(⟨748052398310,748052417639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162967377024,162967377088⟩ : DyadicInterval 40),(⟨-191396879488,-191396879424⟩ : DyadicInterval 40),(⟨748030515429,748030534759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44735746,55958049⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44734784,44734848⟩ : DyadicInterval 40),(⟨-44736704,-44736640⟩ : DyadicInterval 40),(⟨762123382691,762123402020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55956608,55956672⟩ : DyadicInterval 40),(⟨-55959488,-55959424⟩ : DyadicInterval 40),(⟨762123382144,762123401473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175583232962,175708145670⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162897562368,162897562432⟩ : DyadicInterval 40),(⟨-191300522496,-191300522432⟩ : DyadicInterval 40),(⟨748043559772,748043579101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163005269056,163005269120⟩ : DyadicInterval 40),(⟨-191449183616,-191449183552⟩ : DyadicInterval 40),(⟨748023432709,748023452038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28443914496,-28402960000⟩ : DyadicInterval 40),(⟨776324863616,776345360128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2262_ok : ecellOkT e2262 = true := by decide +kernel
theorem e2262_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2262 e2262_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '1599/1600', '1999/2000']  interval_lower 26790767/137438953472
noncomputable def e2263 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275153857747,0,true,162948434240,162948434304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923869397805,0,false,-191370733504,-191370733440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275289720634,0,true,163065576832,163065576896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923733534918,0,false,-191532437952,-191532437888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556393645,0,true,44764928,44764992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466861907,0,false,-44766784,-44766720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567623481,0,true,55994240,55994304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455632071,0,false,-55997184,-55997120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624924,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625954,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275208775974,0,true,162995786880,162995786944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923814479578,0,false,-191436094528,-191436094464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275333695811,0,true,163103490112,163103490176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923689559741,0,false,-191584782464,-191584782400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071396054618,0,false,-28481292352,-28481292288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071435992099,0,false,-28440307584,-28440307520⟩
    { al := (261891/1638400), au := (40947/256000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162948434240,162948434304⟩ : DyadicInterval 40),(⟨-191370733504,-191370733440⟩ : DyadicInterval 40),(⟨748034055420,748034074750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163065576832,163065576896⟩ : DyadicInterval 40),(⟨-191532437952,-191532437888⟩ : DyadicInterval 40),(⟨748012155813,748012175142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44765869,55995705⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44764928,44764992⟩ : DyadicInterval 40),(⟨-44766784,-44766720⟩ : DyadicInterval 40),(⟨762123382657,762123401986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55994240,55994304⟩ : DyadicInterval 40),(⟨-55997184,-55997120⟩ : DyadicInterval 40),(⟨762123382172,762123401501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175697148198,175822068035⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162995786880,162995786944⟩ : DyadicInterval 40),(⟨-191436094528,-191436094464⟩ : DyadicInterval 40),(⟨748025205299,748025224629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163103490112,163103490176⟩ : DyadicInterval 40),(⟨-191584782464,-191584782400⟩ : DyadicInterval 40),(⟨748005063793,748005083123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28481292352,-28440307520⟩ : DyadicInterval 40),(⟨776343537376,776364049056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2263_ok : ecellOkT e2263 = true := by decide +kernel
theorem e2263_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2263 e2263_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '1999/2000', '7997/8000']  interval_lower 205929565/1099511627776
noncomputable def e2264 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274378569626,0,true,162279732480,162279732544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924644685926,0,false,-190448437760,-190448437696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274514347050,0,true,162396872640,162396872704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924508908502,0,false,-190609904960,-190609904896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545044084,0,true,33415744,33415808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478211468,0,false,-33416832,-33416768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556213669,0,true,44584960,44585024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467041883,0,false,-44586816,-44586752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625968,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626761,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274422303832,0,true,162317464960,162317465024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924600951720,0,false,-190500444096,-190500444032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274547176850,0,true,162425194240,162425194304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924476078702,0,false,-190648949888,-190648949824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071647035291,0,false,-28223755584,-28223755520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071686779157,0,false,-28182979072,-28182979008⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162279732480,162279732544⟩ : DyadicInterval 40),(⟨-190448437760,-190448437696⟩ : DyadicInterval 40),(⟨748158693836,748158713166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162396872640,162396872704⟩ : DyadicInterval 40),(⟨-190609904960,-190609904896⟩ : DyadicInterval 40),(⟨748136906221,748136925551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33416308,44585893⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33415744,33415808⟩ : DyadicInterval 40),(⟨-33416832,-33416768⟩ : DyadicInterval 40),(⟨762123383080,762123402409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44584960,44585024⟩ : DyadicInterval 40),(⟨-44586816,-44586752⟩ : DyadicInterval 40),(⟨762123382671,762123402001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174910676056,175035549074⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162317464960,162317465024⟩ : DyadicInterval 40),(⟨-190500444096,-190500444032⟩ : DyadicInterval 40),(⟨748151677861,748151697191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162425194240,162425194304⟩ : DyadicInterval 40),(⟨-190648949888,-190648949824⟩ : DyadicInterval 40),(⟨748131635583,748131654913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28223755584,-28182979008⟩ : DyadicInterval 40),(⟨776214873120,776235280672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2264_ok : ecellOkT e2264 = true := by decide +kernel
theorem e2264_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2264 e2264_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '1999/2000', '7997/8000']  interval_lower 207097487/1099511627776
noncomputable def e2265 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274492463502,0,true,162377993792,162377993856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924530792050,0,false,-190583879360,-190583879296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274628255169,0,true,162495135744,162495135808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924395000383,0,false,-190745383424,-190745383360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545066666,0,true,33438336,33438400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478188886,0,false,-33439424,-33439360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556243781,0,true,44615040,44615104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467011771,0,false,-44616960,-44616896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625965,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626760,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274536226197,0,true,162415747456,162415747520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924487029355,0,false,-190635926016,-190635925952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274661106335,0,true,162523473216,162523473280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924362149217,0,false,-190784458560,-190784458496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071610749727,0,false,-28260985280,-28260985216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071650521738,0,false,-28220178496,-28220178432⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162377993792,162377993856⟩ : DyadicInterval 40),(⟨-190583879360,-190583879296⟩ : DyadicInterval 40),(⟨748140418927,748140438257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162495135744,162495135808⟩ : DyadicInterval 40),(⟨-190745383424,-190745383360⟩ : DyadicInterval 40),(⟨748118614622,748118633952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33438890,44616005⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33438336,33438400⟩ : DyadicInterval 40),(⟨-33439424,-33439360⟩ : DyadicInterval 40),(⟨762123383079,762123402408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44615040,44615104⟩ : DyadicInterval 40),(⟨-44616960,-44616896⟩ : DyadicInterval 40),(⟨762123382701,762123402030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175024598421,175149478559⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162415747456,162415747520⟩ : DyadicInterval 40),(⟨-190635926016,-190635925952⟩ : DyadicInterval 40),(⟨748133393755,748133413084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162523473216,162523473280⟩ : DyadicInterval 40),(⟨-190784458560,-190784458496⟩ : DyadicInterval 40),(⟨748113337070,748113356400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28260985280,-28220178432⟩ : DyadicInterval 40),(⟨776233472832,776253895520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2265_ok : ecellOkT e2265 = true := by decide +kernel
theorem e2265_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2265 e2265_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '7997/8000', '3999/4000']  interval_lower 205762411/1099511627776
noncomputable def e2266 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274400438928,0,true,162298600832,162298600896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924622816624,0,false,-190474443200,-190474443136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274536230596,0,true,162415751232,162415751296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924487024956,0,false,-190635931200,-190635931136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533905282,0,true,22277248,22277312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489350270,0,false,-22277760,-22277696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545067339,0,true,33439040,33439104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478188213,0,false,-33440128,-33440064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626758,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627325,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274433238400,0,true,162326898752,162326898816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924590017152,0,false,-190513447296,-190513447232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274558118562,0,true,162434633280,162434633344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924465136990,0,false,-190661963328,-190661963264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071643551475,0,false,-28227330048,-28227329984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071683300099,0,false,-28186548480,-28186548416⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162298600832,162298600896⟩ : DyadicInterval 40),(⟨-190474443200,-190474443136⟩ : DyadicInterval 40),(⟨748155185673,748155205003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162415751232,162415751296⟩ : DyadicInterval 40),(⟨-190635931200,-190635931136⟩ : DyadicInterval 40),(⟨748133393040,748133412369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22277506,33439563⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22277248,22277312⟩ : DyadicInterval 40),(⟨-22277760,-22277696⟩ : DyadicInterval 40),(⟨762123383356,762123402685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33439040,33439104⟩ : DyadicInterval 40),(⟨-33440128,-33440064⟩ : DyadicInterval 40),(⟨762123383078,762123402408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174921610624,175046490786⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162326898752,162326898816⟩ : DyadicInterval 40),(⟨-190513447296,-190513447232⟩ : DyadicInterval 40),(⟨748149923437,748149942766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162434633280,162434633344⟩ : DyadicInterval 40),(⟨-190661963328,-190661963264⟩ : DyadicInterval 40),(⟨748129878727,748129898056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28227330048,-28186548416⟩ : DyadicInterval 40),(⟨776216657824,776237067904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2266_ok : ecellOkT e2266 = true := by decide +kernel
theorem e2266_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2266 e2266_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '7997/8000', '3999/4000']  interval_lower 206929771/1099511627776
noncomputable def e2267 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274514347048,0,true,162396872640,162396872704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924508908504,0,false,-190609904960,-190609904896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274650152959,0,true,162514024896,162514024960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924373102593,0,false,-190771429824,-190771429760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533920336,0,true,22292288,22292352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489335216,0,false,-22292800,-22292736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545089923,0,true,33461632,33461696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478165629,0,false,-33462720,-33462656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626757,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627325,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274547167879,0,true,162425186496,162425186560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924476087673,0,false,-190648939264,-190648939200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274672055166,0,true,162532917568,162532917632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924351200386,0,false,-190797482048,-190797481984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071607261375,0,false,-28264564480,-28264564416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071647038149,0,false,-28223752704,-28223752640⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162396872640,162396872704⟩ : DyadicInterval 40),(⟨-190609904960,-190609904896⟩ : DyadicInterval 40),(⟨748136906222,748136925551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162514024896,162514024960⟩ : DyadicInterval 40),(⟨-190771429824,-190771429760⟩ : DyadicInterval 40),(⟨748115096853,748115116183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22292560,33462147⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22292288,22292352⟩ : DyadicInterval 40),(⟨-22292800,-22292736⟩ : DyadicInterval 40),(⟨762123383356,762123402685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33461632,33461696⟩ : DyadicInterval 40),(⟨-33462720,-33462656⟩ : DyadicInterval 40),(⟨762123383077,762123402406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175035540103,175160427390⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162425186496,162425186560⟩ : DyadicInterval 40),(⟨-190648939264,-190648939200⟩ : DyadicInterval 40),(⟨748131637046,748131656376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162532917568,162532917632⟩ : DyadicInterval 40),(⟨-190797482048,-190797481984⟩ : DyadicInterval 40),(⟨748111577887,748111597217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28264564480,-28223752640⟩ : DyadicInterval 40),(⟨776235259936,776255685120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2267_ok : ecellOkT e2267 = true := by decide +kernel
theorem e2267_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2267 e2267_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '1999/2000', '7997/8000']  interval_lower 208267957/1099511627776
noncomputable def e2268 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274606357377,0,true,162476246272,162476246336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924416898175,0,false,-190719337600,-190719337536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274742163289,0,true,162593390016,162593390080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924281092263,0,false,-190880878528,-190880878464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545089250,0,true,33460928,33460992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478166302,0,false,-33462016,-33461952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556273895,0,true,44645184,44645248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466981657,0,false,-44647040,-44646976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625963,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626758,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274650148558,0,true,162514021120,162514021184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924373106994,0,false,-190771424576,-190771424512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274775035821,0,true,162621743424,162621743488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924248219731,0,false,-190919983936,-190919983872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071574440552,0,false,-28298240448,-28298240384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071614240712,0,false,-28257403392,-28257403328⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162476246272,162476246336⟩ : DyadicInterval 40),(⟨-190719337600,-190719337536⟩ : DyadicInterval 40),(⟨748122131924,748122151254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162593390016,162593390080⟩ : DyadicInterval 40),(⟨-190880878528,-190880878464⟩ : DyadicInterval 40),(⟨748100310921,748100330251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33461474,44646119⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33460928,33460992⟩ : DyadicInterval 40),(⟨-33462016,-33461952⟩ : DyadicInterval 40),(⟨762123383077,762123402406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44645184,44645248⟩ : DyadicInterval 40),(⟨-44647040,-44646976⟩ : DyadicInterval 40),(⟨762123382667,762123401996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175138520782,175263408045⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162514021120,162514021184⟩ : DyadicInterval 40),(⟨-190771424576,-190771424512⟩ : DyadicInterval 40),(⟨748115097543,748115116872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162621743424,162621743488⟩ : DyadicInterval 40),(⟨-190919983936,-190919983872⟩ : DyadicInterval 40),(⟨748095026436,748095045765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28298240448,-28257403328⟩ : DyadicInterval 40),(⟨776252085280,776272523104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2268_ok : ecellOkT e2268 = true := by decide +kernel
theorem e2268_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2268 e2268_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '1999/2000', '7997/8000']  interval_lower 6545051/34359738368
noncomputable def e2269 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274720251253,0,true,162574489984,162574490048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924303004299,0,false,-190854812608,-190854812544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274856071409,0,true,162691635584,162691635648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924167184143,0,false,-191016390336,-191016390272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545111834,0,true,33483520,33483584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478143718,0,false,-33484608,-33484544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556304011,0,true,44675264,44675328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466951541,0,false,-44677184,-44677120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625960,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626757,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274764070919,0,true,162612286016,162612286080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924259184633,0,false,-190906939840,-190906939776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274888965312,0,true,162720004864,162720004928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924134290240,0,false,-191055526016,-191055525952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071538107765,0,false,-28335521088,-28335521024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071577936079,0,false,-28294653824,-28294653760⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162574489984,162574490048⟩ : DyadicInterval 40),(⟨-190854812608,-190854812544⟩ : DyadicInterval 40),(⟨748103832842,748103852172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162691635584,162691635648⟩ : DyadicInterval 40),(⟨-191016390336,-191016390272⟩ : DyadicInterval 40),(⟨748081995070,748082014400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33484058,44676235⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33483520,33483584⟩ : DyadicInterval 40),(⟨-33484608,-33484544⟩ : DyadicInterval 40),(⟨762123383076,762123402405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44675264,44675328⟩ : DyadicInterval 40),(⟨-44677184,-44677120⟩ : DyadicInterval 40),(⟨762123382696,762123402025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175252443143,175377337536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162612286016,162612286080⟩ : DyadicInterval 40),(⟨-190906939840,-190906939776⟩ : DyadicInterval 40),(⟨748096789213,748096808542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162720004864,162720004928⟩ : DyadicInterval 40),(⟨-191055526016,-191055525952⟩ : DyadicInterval 40),(⟨748076703678,748076723007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28335521088,-28294653760⟩ : DyadicInterval 40),(⟨776270710496,776291163424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2269_ok : ecellOkT e2269 = true := by decide +kernel
theorem e2269_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2269 e2269_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '7997/8000', '3999/4000']  interval_lower 208099937/1099511627776
noncomputable def e2270 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274628255167,0,true,162495135744,162495135808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924395000385,0,false,-190745383424,-190745383360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274764075323,0,true,162612289792,162612289856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924259180229,0,false,-190906945088,-190906945024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533935392,0,true,22307328,22307392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489320160,0,false,-22307904,-22307840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545112508,0,true,33484160,33484224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478143044,0,false,-33485248,-33485184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626756,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627324,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274661097362,0,true,162523465472,162523465536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924362158190,0,false,-190784447872,-190784447808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274785991774,0,true,162631193088,162631193152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924237263778,0,false,-190933017536,-190933017472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071570947660,0,false,-28301824448,-28301824384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071610752587,0,false,-28260982336,-28260982272⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162495135744,162495135808⟩ : DyadicInterval 40),(⟨-190745383424,-190745383360⟩ : DyadicInterval 40),(⟨748118614622,748118633952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162612289792,162612289856⟩ : DyadicInterval 40),(⟨-190906945088,-190906945024⟩ : DyadicInterval 40),(⟨748096788522,748096807851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22307616,33484732⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22307328,22307392⟩ : DyadicInterval 40),(⟨-22307904,-22307840⟩ : DyadicInterval 40),(⟨762123383387,762123402716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33484160,33484224⟩ : DyadicInterval 40),(⟨-33485248,-33485184⟩ : DyadicInterval 40),(⟨762123383076,762123402405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175149469586,175274363998⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162523465472,162523465536⟩ : DyadicInterval 40),(⟨-190784447872,-190784447808⟩ : DyadicInterval 40),(⟨748113338508,748113357838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162631193088,162631193152⟩ : DyadicInterval 40),(⟨-190933017536,-190933017472⟩ : DyadicInterval 40),(⟨748093264950,748093284280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28301824448,-28260982272⟩ : DyadicInterval 40),(⟨776253874752,776274315104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2270_ok : ecellOkT e2270 = true := by decide +kernel
theorem e2270_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2270 e2270_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '7997/8000', '3999/4000']  interval_lower 26159127/137438953472
noncomputable def e2271 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274742163287,0,true,162593390016,162593390080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924281092265,0,false,-190880878528,-190880878464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274877997687,0,true,162710545920,162710545984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924145257865,0,false,-191042477056,-191042476992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533950449,0,true,22322432,22322496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489305103,0,false,-22322944,-22322880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545135095,0,true,33506752,33506816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478120457,0,false,-33507840,-33507776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626754,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627323,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274775026845,0,true,162621735680,162621735744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924248228707,0,false,-190919973248,-190919973184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274899928386,0,true,162729459776,162729459840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924123327166,0,false,-191068569664,-191068569600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071534610331,0,false,-28339109824,-28339109760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071574443415,0,false,-28298237504,-28298237440⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162593390016,162593390080⟩ : DyadicInterval 40),(⟨-190880878528,-190880878464⟩ : DyadicInterval 40),(⟨748100310921,748100330251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162710545920,162710545984⟩ : DyadicInterval 40),(⟨-191042477056,-191042476992⟩ : DyadicInterval 40),(⟨748078468071,748078487401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22322673,33507319⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22322432,22322496⟩ : DyadicInterval 40),(⟨-22322944,-22322880⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33506752,33506816⟩ : DyadicInterval 40),(⟨-33507840,-33507776⟩ : DyadicInterval 40),(⟨762123383074,762123402403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175263399069,175388300610⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162621735680,162621735744⟩ : DyadicInterval 40),(⟨-190919973248,-190919973184⟩ : DyadicInterval 40),(⟨748095027876,748095047205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162729459776,162729459840⟩ : DyadicInterval 40),(⟨-191068569664,-191068569600⟩ : DyadicInterval 40),(⟨748074939897,748074959227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28339109824,-28298237440⟩ : DyadicInterval 40),(⟨776272502336,776292957792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2271_ok : ecellOkT e2271 = true := by decide +kernel
theorem e2271_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2271 e2271_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '3999/4000', '7999/8000']  interval_lower 205594977/1099511627776
noncomputable def e2272 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274422308231,0,true,162317468800,162317468864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924600947321,0,false,-190500449344,-190500449280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274558114142,0,true,162434629504,162434629568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924465141410,0,false,-190661958080,-190661958016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522766427,0,true,11138560,11138624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500489125,0,false,-11138752,-11138688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533920957,0,true,22292928,22292992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489334595,0,false,-22293440,-22293376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627323,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274444172987,0,true,162336332480,162336332544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924579082565,0,false,-190526450624,-190526450560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274569060298,0,true,162444072256,162444072320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924454195254,0,false,-190674976960,-190674976896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071640067433,0,false,-28230904640,-28230904576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071679820817,0,false,-28190118144,-28190118080⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174954419060,175068369912⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162317468800,162317468864⟩ : DyadicInterval 40),(⟨-190500449344,-190500449280⟩ : DyadicInterval 40),(⟨748151677136,748151696466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162434629504,162434629568⟩ : DyadicInterval 40),(⟨-190661958080,-190661958016⟩ : DyadicInterval 40),(⟨748129879419,748129898748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11138651,22293181⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11138560,11138624⟩ : DyadicInterval 40),(⟨-11138752,-11138688⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22292928,22292992⟩ : DyadicInterval 40),(⟨-22293440,-22293376⟩ : DyadicInterval 40),(⟨762123383355,762123402684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174932545211,175057432522⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162336332480,162336332544⟩ : DyadicInterval 40),(⟨-190526450624,-190526450560⟩ : DyadicInterval 40),(⟨748148168877,748148188206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162444072256,162444072320⟩ : DyadicInterval 40),(⟨-190674976960,-190674976896⟩ : DyadicInterval 40),(⟨748128121760,748128141090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28230904640,-28190118080⟩ : DyadicInterval 40),(⟨776218442656,776238855200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2272_ok : ecellOkT e2272 = true := by decide +kernel
theorem e2272_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2272 e2272_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '3999/4000', '7999/8000']  interval_lower 206761951/1099511627776
noncomputable def e2273 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274536230594,0,true,162415751232,162415751296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924487024958,0,false,-190635931200,-190635931136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274672050749,0,true,162532913728,162532913792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924351204803,0,false,-190797476800,-190797476736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522773954,0,true,11146112,11146176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500481598,0,false,-11146240,-11146176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533936012,0,true,22307968,22308032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489319540,0,false,-22308480,-22308416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627323,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274558109591,0,true,162434625536,162434625600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924465145961,0,false,-190661952640,-190661952576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274683004024,0,true,162542361856,162542361920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924340251528,0,false,-190810505792,-190810505728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071603772796,0,false,-28268143872,-28268143808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071643554332,0,false,-28227327104,-28227327040⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175068369911,175182320763⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162415751232,162415751296⟩ : DyadicInterval 40),(⟨-190635931200,-190635931136⟩ : DyadicInterval 40),(⟨748133393040,748133412370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162532913728,162532913792⟩ : DyadicInterval 40),(⟨-190797476800,-190797476736⟩ : DyadicInterval 40),(⟨748111578617,748111597946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11146178,22308236⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11146112,11146176⟩ : DyadicInterval 40),(⟨-11146240,-11146176⟩ : DyadicInterval 40),(⟨762123383503,762123402832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22307968,22308032⟩ : DyadicInterval 40),(⟨-22308480,-22308416⟩ : DyadicInterval 40),(⟨762123383355,762123402684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175046481815,175171376248⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162434625536,162434625600⟩ : DyadicInterval 40),(⟨-190661952640,-190661952576⟩ : DyadicInterval 40),(⟨748129880162,748129899492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162542361856,162542361920⟩ : DyadicInterval 40),(⟨-190810505792,-190810505728⟩ : DyadicInterval 40),(⟨748109818621,748109837951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28268143872,-28227327040⟩ : DyadicInterval 40),(⟨776237047136,776257474816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2273_ok : ecellOkT e2273 = true := by decide +kernel
theorem e2273_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2273 e2273_ok ha1 ha2 hz1 hz2 hz

-- box ['162939/1024000', '1304361/8192000', '7999/8000', '1']  interval_lower 205427477/1099511627776
noncomputable def e2274 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046836,0,true,162355203712,162355203776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208716,0,false,-190552463360,-190552463296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997688,0,true,162453507392,162453507456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257864,0,false,-190687985536,-190687985472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274444177533,0,true,162336336384,162336336448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924579078019,0,false,-190526456064,-190526456000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522774521,0,true,11146688,11146752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500481031,0,false,-11146816,-11146752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274455107595,0,true,162345766144,162345766208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924568147957,0,false,-190539454208,-190539454144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274580002058,0,true,162453511168,162453511232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924443253494,0,false,-190687990784,-190687990720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071636583165,0,false,-28234479552,-28234479488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071676341311,0,false,-28193688000,-28193687936⟩
    { al := (162939/1024000), au := (1304361/8192000), zl := (7999/8000), zu := 1,
      A := ⟨174954419060,175068369912⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162336336384,162336336448⟩ : DyadicInterval 40),(⟨-190526456064,-190526456000⟩ : DyadicInterval 40),(⟨748148168172,748148187502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11146745⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11146688,11146752⟩ : DyadicInterval 40),(⟨-11146816,-11146752⟩ : DyadicInterval 40),(⟨762123383502,762123402831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174943479819,175068374282⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162345766144,162345766208⟩ : DyadicInterval 40),(⟨-190539454208,-190539454144⟩ : DyadicInterval 40),(⟨748146414235,748146433564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453511168,162453511232⟩ : DyadicInterval 40),(⟨-190687990784,-190687990720⟩ : DyadicInterval 40),(⟨748126364685,748126384014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28234479552,-28193687936⟩ : DyadicInterval 40),(⟨776220227584,776240642656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162355203712,162453507456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190687985536,-190552463296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2274_ok : ecellOkT e2274 = true := by decide +kernel
theorem e2274_pos {a z : ℝ} (ha1 : ((162939/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1304361/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2274 e2274_ok ha1 ha2 hz1 hz2 hz

-- box ['1304361/8192000', '130521/819200', '7999/8000', '1']  interval_lower 103293319/549755813888
noncomputable def e2275 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274579997687,0,true,162453507392,162453507456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924443257865,0,false,-190687985536,-190687985472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948539,0,true,162551802304,162551802368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307013,0,false,-190823524480,-190823524416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274558114140,0,true,162434629504,162434629568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924465141412,0,false,-190661958080,-190661958016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522782049,0,true,11154176,11154240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500473503,0,false,-11154368,-11154304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274569051327,0,true,162444064512,162444064576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924454204225,0,false,-190674966272,-190674966208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693957003,0,true,162551809600,162551809664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924329298549,0,false,-190823534528,-190823534464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071600282685,0,false,-28271724928,-28271724864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071640070290,0,false,-28230901760,-28230901696⟩
    { al := (1304361/8192000), au := (130521/819200), zl := (7999/8000), zu := 1,
      A := ⟨175068369911,175182320763⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162453507392,162453507456⟩ : DyadicInterval 40),(⟨-190687985536,-190687985472⟩ : DyadicInterval 40),(⟨748126365369,748126384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162434629504,162434629568⟩ : DyadicInterval 40),(⟨-190661958080,-190661958016⟩ : DyadicInterval 40),(⟨748129879419,748129898749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11154273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11154176,11154240⟩ : DyadicInterval 40),(⟨-11154368,-11154304⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175057423551,175182329227⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162444064512,162444064576⟩ : DyadicInterval 40),(⟨-190674966272,-190674966208⟩ : DyadicInterval 40),(⟨748128123196,748128142526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551809600,162551809664⟩ : DyadicInterval 40),(⟨-190823534528,-190823534464⟩ : DyadicInterval 40),(⟨748108058565,748108077894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28271724928,-28230901696⟩ : DyadicInterval 40),(⟨776238834464,776259265344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162453507392,162551802368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190823524480,-190687985472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2275_ok : ecellOkT e2275 = true := by decide +kernel
theorem e2275_pos {a z : ℝ} (ha1 : ((1304361/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130521/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2275 e2275_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '3999/4000', '7999/8000']  interval_lower 103965797/549755813888
noncomputable def e2276 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274650152957,0,true,162514024896,162514024960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924373102595,0,false,-190771429824,-190771429760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274785987357,0,true,162631189248,162631189312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924237268195,0,false,-190933012288,-190933012224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522781482,0,true,11153600,11153664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500474070,0,false,-11153792,-11153728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533951069,0,true,22323008,22323072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489304483,0,false,-22323520,-22323456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627322,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274672046192,0,true,162532909824,162532909888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924351209360,0,false,-190797471424,-190797471360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274796947753,0,true,162640642624,162640642688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924226307799,0,false,-190946051264,-190946051200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071567454541,0,false,-28305408640,-28305408576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071607264235,0,false,-28264561536,-28264561472⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175182320762,175296271614⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162514024896,162514024960⟩ : DyadicInterval 40),(⟨-190771429824,-190771429760⟩ : DyadicInterval 40),(⟨748115096853,748115116183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162631189248,162631189312⟩ : DyadicInterval 40),(⟨-190933012288,-190933012224⟩ : DyadicInterval 40),(⟨748093265681,748093285010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11153706,22323293⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11153600,11153664⟩ : DyadicInterval 40),(⟨-11153792,-11153728⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22323008,22323072⟩ : DyadicInterval 40),(⟨-22323520,-22323456⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175160418416,175285319977⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162532909824,162532909888⟩ : DyadicInterval 40),(⟨-190797471424,-190797471360⟩ : DyadicInterval 40),(⟨748111579353,748111598682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162640642624,162640642688⟩ : DyadicInterval 40),(⟨-190946051264,-190946051200⟩ : DyadicInterval 40),(⟨748091503365,748091522695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28305408640,-28264561472⟩ : DyadicInterval 40),(⟨776255664352,776276107200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2276_ok : ecellOkT e2276 = true := by decide +kernel
theorem e2276_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2276 e2276_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '3999/4000', '7999/8000']  interval_lower 52274181/274877906944
noncomputable def e2277 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274764075321,0,true,162612289792,162612289856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924259180231,0,false,-190906945088,-190906945024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274899923965,0,true,162729455936,162729456000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924123331587,0,false,-191068564416,-191068564352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522789009,0,true,11161152,11161216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500466543,0,false,-11161344,-11161280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533966127,0,true,22338112,22338176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489289425,0,false,-22338624,-22338560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627322,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274785982798,0,true,162631185344,162631185408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924237272754,0,false,-190933006848,-190933006784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274910895580,0,true,162738918144,162738918208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924112359972,0,false,-191081618368,-191081618304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071531111363,0,false,-28342700160,-28342700096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071570950523,0,false,-28301821504,-28301821440⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175296271613,175410222466⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162612289792,162612289856⟩ : DyadicInterval 40),(⟨-190906945088,-190906945024⟩ : DyadicInterval 40),(⟨748096788522,748096807852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162729455936,162729456000⟩ : DyadicInterval 40),(⟨-191068564416,-191068564352⟩ : DyadicInterval 40),(⟨748074940629,748074959958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11161233,22338351⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11161152,11161216⟩ : DyadicInterval 40),(⟨-11161344,-11161280⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22338112,22338176⟩ : DyadicInterval 40),(⟨-22338624,-22338560⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175274355022,175399267804⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162631185344,162631185408⟩ : DyadicInterval 40),(⟨-190933006848,-190933006784⟩ : DyadicInterval 40),(⟨748093266391,748093285720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162738918144,162738918208⟩ : DyadicInterval 40),(⟨-191081618368,-191081618304⟩ : DyadicInterval 40),(⟨748073175350,748073194680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28342700160,-28301821440⟩ : DyadicInterval 40),(⟨776274294336,776294752960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2277_ok : ecellOkT e2277 = true := by decide +kernel
theorem e2277_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2277 e2277_ok ha1 ha2 hz1 hz2 hz

-- box ['130521/819200', '1306059/8192000', '7999/8000', '1']  interval_lower 207763755/1099511627776
noncomputable def e2278 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274693948538,0,true,162551802304,162551802368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924329307014,0,false,-190823524480,-190823524416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899390,0,true,162650088384,162650088448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356162,0,false,-190959080064,-190959080000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274672050747,0,true,162532913728,162532913792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924351204805,0,false,-190797476800,-190797476736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522789578,0,true,11161728,11161792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500465974,0,false,-11161920,-11161856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274682995050,0,true,162542354112,162542354176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924340260502,0,false,-190810495104,-190810495040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807903758,0,true,162650092160,162650092224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924215351794,0,false,-190959085248,-190959085184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071563961196,0,false,-28308993088,-28308993024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071603775656,0,false,-28268140992,-28268140928⟩
    { al := (130521/819200), au := (1306059/8192000), zl := (7999/8000), zu := 1,
      A := ⟨175182320762,175296271614⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162551802304,162551802368⟩ : DyadicInterval 40),(⟨-190823524480,-190823524416⟩ : DyadicInterval 40),(⟨748108059930,748108079260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162532913728,162532913792⟩ : DyadicInterval 40),(⟨-190797476800,-190797476736⟩ : DyadicInterval 40),(⟨748111578617,748111597947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11161802⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11161728,11161792⟩ : DyadicInterval 40),(⟨-11161920,-11161856⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175171367274,175296275982⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162542354112,162542354176⟩ : DyadicInterval 40),(⟨-190810495104,-190810495040⟩ : DyadicInterval 40),(⟨748109820060,748109839389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650092160,162650092224⟩ : DyadicInterval 40),(⟨-190959085248,-190959085184⟩ : DyadicInterval 40),(⟨748089741659,748089760988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28308993088,-28268140928⟩ : DyadicInterval 40),(⟨776257454080,776277899424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162551802304,162650088448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190959080064,-190823524416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2278_ok : ecellOkT e2278 = true := by decide +kernel
theorem e2278_pos {a z : ℝ} (ha1 : ((130521/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1306059/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2278 e2278_ok ha1 ha2 hz1 hz2 hz

-- box ['1306059/8192000', '326727/2048000', '7999/8000', '1']  interval_lower 208936009/1099511627776
noncomputable def e2279 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274807899389,0,true,162650088384,162650088448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924215356163,0,false,-190959080064,-190959080000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850242,0,true,162748365696,162748365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405310,0,false,-191094652352,-191094652288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274785987354,0,true,162631189248,162631189312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924237268198,0,false,-190933012224,-190933012160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522797106,0,true,11169216,11169280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500458446,0,false,-11169408,-11169344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274796938779,0,true,162640634880,162640634944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924226316773,0,false,-190946040576,-190946040512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921854613,0,true,162748369472,162748369536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨924101400939,0,false,-191094657536,-191094657472⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071527614781,0,false,-28346288064,-28346288000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071567457404,0,false,-28305405696,-28305405632⟩
    { al := (1306059/8192000), au := (326727/2048000), zl := (7999/8000), zu := 1,
      A := ⟨175296271613,175410222466⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162650088384,162650088448⟩ : DyadicInterval 40),(⟨-190959080064,-190959080000⟩ : DyadicInterval 40),(⟨748089742371,748089761701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162631189248,162631189312⟩ : DyadicInterval 40),(⟨-190933012224,-190933012160⟩ : DyadicInterval 40),(⟨748093265654,748093284984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412680,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11169330⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11169216,11169280⟩ : DyadicInterval 40),(⟨-11169408,-11169344⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175285311003,175410226837⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162640634880,162640634944⟩ : DyadicInterval 40),(⟨-190946040576,-190946040512⟩ : DyadicInterval 40),(⟨748091504805,748091524135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748369472,162748369536⟩ : DyadicInterval 40),(⟨-191094657536,-191094657472⟩ : DyadicInterval 40),(⟨748071411966,748071431296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28346288064,-28305405632⟩ : DyadicInterval 40),(⟨776276086432,776296546912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162650088384,162748365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191094652352,-190959080000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2279_ok : ecellOkT e2279 = true := by decide +kernel
theorem e2279_pos {a z : ℝ} (ha1 : ((1306059/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((326727/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2279 e2279_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B037

end


