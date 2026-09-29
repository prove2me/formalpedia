-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B003__2_q00
-- name    : CK_CKLaneC2R_EpCells_B003__2_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:14:53.6372+00:00
-- url     : https://prove2.me/theorems/a8356a0d-b2cc-4f54-9e8f-55d32e33a9cf
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B003 (+1 modules: CKLaneC2R/EpCells/B004) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B003 =====
section

namespace CKLaneC2R.EpCells.B003

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['295383/1024000', '37029/128000', '999/1000', '1']  interval_lower 683707583/1099511627776
noncomputable def e180 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1416676708974,0,true,278668667264,278668667328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨782346546578,0,false,-374189743232,-374189743168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1417588315784,0,true,279375956352,279375956416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨781434939768,0,false,-375471664512,-375471664448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1416359543892,0,true,278422481408,278422481472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨782663711660,0,false,-373744089024,-373744088960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099681041202,0,true,169400320,169400384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099342214350,0,false,-169426496,-169426432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511601672,0,false,-26112,-26048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1416518123700,0,true,278545579136,278545579200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨782505131852,0,false,-373966889664,-373966889600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1417588324455,0,true,279375963072,279375963136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨781434931097,0,false,-375471676736,-375471676672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1007495515881,0,false,-96095713600,-96095713536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1008113668974,0,false,-95421310528,-95421310464⟩
    { al := (295383/1024000), au := (37029/128000), zl := (999/1000), zu := 1,
      A := ⟨317165081198,318076688008⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨278668667264,278668667328⟩ : DyadicInterval 40),(⟨-374189743232,-374189743168⟩ : DyadicInterval 40),(⟨715722165741,715722185070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279375956352,279375956416⟩ : DyadicInterval 40),(⟨-375471664512,-375471664448⟩ : DyadicInterval 40),(⟨715451110471,715451129800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨278422481408,278422481472⟩ : DyadicInterval 40),(⟨-373744089024,-373744088960⟩ : DyadicInterval 40),(⟨715816277615,715816296945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279375956352,279375956416⟩ : DyadicInterval 40),(⟨-375471664512,-375471664448⟩ : DyadicInterval 40),(⟨715451110471,715451129800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,169413426⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169400320,169400384⟩ : DyadicInterval 40),(⟨-169426496,-169426432⟩ : DyadicInterval 40),(⟨762123370536,762123389865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26112,0⟩ : DyadicInterval 40),(⟨762123383616,762123415936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨317006495924,318076696679⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨278545579136,278545579200⟩ : DyadicInterval 40),(⟨-373966889664,-373966889600⟩ : DyadicInterval 40),(⟨715769234926,715769254256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279375963072,279375963136⟩ : DyadicInterval 40),(⟨-375471676736,-375471676672⟩ : DyadicInterval 40),(⟨715451107900,715451127230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-96095713600,-95421310464⟩ : DyadicInterval 40),(⟨809834038848,810171259680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨278668667264,279375956416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-375471664512,-374189743168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e180_ok : ecellOkT e180 = true := by decide +kernel
theorem e180_pos {a z : ℝ} (ha1 : ((295383/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((37029/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e180 e180_ok ha1 ha2 hz1 hz2 hz

-- box ['37029/128000', '297081/1024000', '999/1000', '1']  interval_lower 739278611/1099511627776
noncomputable def e181 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1417588315783,0,true,279375956352,279375956416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨781434939769,0,false,-375471664512,-375471664448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1418499922592,0,true,280082790720,280082790784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨780523332960,0,false,-376755082176,-376755082112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1417270239094,0,true,279129221632,279129221696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨781753016458,0,false,-375024208384,-375024208320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099681591327,0,true,169950400,169950464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099341664225,0,false,-169976704,-169976640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511601502,0,false,-26304,-26240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1417429274743,0,true,279252593792,279252593856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨781593980809,0,false,-375247909888,-375247909824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1418499931260,0,true,280082797440,280082797504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨780523324292,0,false,-376755094336,-376755094272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1006967324296,0,false,-96672296896,-96672296832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1007587515562,0,false,-95995316032,-95995315968⟩
    { al := (37029/128000), au := (297081/1024000), zl := (999/1000), zu := 1,
      A := ⟨318076688007,318988294816⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279375956352,279375956416⟩ : DyadicInterval 40),(⟨-375471664512,-375471664448⟩ : DyadicInterval 40),(⟨715451110471,715451129801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280082790720,280082790784⟩ : DyadicInterval 40),(⟨-376755082176,-376755082112⟩ : DyadicInterval 40),(⟨715179230394,715179249723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279129221632,279129221696⟩ : DyadicInterval 40),(⟨-375024208384,-375024208320⟩ : DyadicInterval 40),(⟨715545780394,715545799723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280082790720,280082790784⟩ : DyadicInterval 40),(⟨-376755082176,-376755082112⟩ : DyadicInterval 40),(⟨715179230394,715179249723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,169963551⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169950400,169950464⟩ : DyadicInterval 40),(⟨-169976704,-169976640⟩ : DyadicInterval 40),(⟨762123370430,762123389759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26304,0⟩ : DyadicInterval 40),(⟨762123383616,762123416032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨317917646967,318988303484⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279252593792,279252593856⟩ : DyadicInterval 40),(⟨-375247909888,-375247909824⟩ : DyadicInterval 40),(⟨715498458804,715498478133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280082797440,280082797504⟩ : DyadicInterval 40),(⟨-376755094336,-376755094272⟩ : DyadicInterval 40),(⟨715179227786,715179247115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-96672296896,-95995315968⟩ : DyadicInterval 40),(⟨810121041600,810459551328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨279375956352,280082790784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-376755082176,-375471664448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e181_ok : ecellOkT e181 = true := by decide +kernel
theorem e181_pos {a z : ℝ} (ha1 : ((37029/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((297081/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e181 e181_ok ha1 ha2 hz1 hz2 hz

-- box ['297081/1024000', '29793/102400', '999/1000', '1']  interval_lower 24862075/34359738368
noncomputable def e182 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1418499922591,0,true,280082790720,280082790784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨780523332961,0,false,-376755082176,-376755082112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1419411529401,0,true,280789170944,280789171008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨779611726151,0,false,-378039999616,-378039999552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1418180934296,0,true,279835507776,279835507840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨780842321256,0,false,-376305819904,-376305819840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099682142068,0,true,170501056,170501120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099341113484,0,false,-170527552,-170527488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511601332,0,false,-26496,-26432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1418340425764,0,true,279959154112,279959154176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨780682829788,0,false,-376530424320,-376530424256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1419411538065,0,true,280789177664,280789177728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨779611717487,0,false,-378040011840,-378040011776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1006437621082,0,false,-97250834112,-97250834048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1007059852044,0,false,-96571270144,-96571270080⟩
    { al := (297081/1024000), au := (29793/102400), zl := (999/1000), zu := 1,
      A := ⟨318988294815,319899901625⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280082790720,280082790784⟩ : DyadicInterval 40),(⟨-376755082176,-376755082112⟩ : DyadicInterval 40),(⟨715179230394,715179249724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280789170944,280789171008⟩ : DyadicInterval 40),(⟨-378039999616,-378039999552⟩ : DyadicInterval 40),(⟨714906525043,714906544372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279835507776,279835507840⟩ : DyadicInterval 40),(⟨-376305819904,-376305819840⟩ : DyadicInterval 40),(⟨715274460198,715274479528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280789170944,280789171008⟩ : DyadicInterval 40),(⟨-378039999616,-378039999552⟩ : DyadicInterval 40),(⟨714906525043,714906544372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,170514292⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170501056,170501120⟩ : DyadicInterval 40),(⟨-170527552,-170527488⟩ : DyadicInterval 40),(⟨762123370356,762123389685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26496,0⟩ : DyadicInterval 40),(⟨762123383616,762123416128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨318828797988,319899910289⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨279959154112,279959154176⟩ : DyadicInterval 40),(⟨-376530424320,-376530424256⟩ : DyadicInterval 40),(⟨715226858733,715226878062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280789177664,280789177728⟩ : DyadicInterval 40),(⟨-378040011840,-378040011776⟩ : DyadicInterval 40),(⟨714906522443,714906541773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-97250834112,-96571270080⟩ : DyadicInterval 40),(⟨810409018656,810748819936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨280082790720,280789171008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-378039999616,-376755082112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e182_ok : ecellOkT e182 = true := by decide +kernel
theorem e182_pos {a z : ℝ} (ha1 : ((297081/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((29793/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e182 e182_ok ha1 ha2 hz1 hz2 hz

-- box ['29793/102400', '298779/1024000', '999/1000', '1']  interval_lower 852636975/1099511627776
noncomputable def e183 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1419411529400,0,true,280789170944,280789171008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨779611726152,0,false,-378039999616,-378039999552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1420323136209,0,true,281495097728,281495097792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨778700119343,0,false,-379326420416,-379326420352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1419091629498,0,true,280541340608,280541340672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨779931626054,0,false,-377588926976,-377588926912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099682693427,0,true,171052288,171052352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099340562125,0,false,-171078976,-171078912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511601161,0,false,-26624,-26560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1419251576802,0,true,280665260672,280665260736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨779771678750,0,false,-377814436416,-377814436352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1420323144888,0,true,281495104448,281495104512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨778700110664,0,false,-379326432704,-379326432640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1005906406228,0,false,-97831328256,-97831328192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1006530678398,0,false,-97149175680,-97149175616⟩
    { al := (29793/102400), au := (298779/1024000), zl := (999/1000), zu := 1,
      A := ⟨319899901624,320811508433⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280789170944,280789171008⟩ : DyadicInterval 40),(⟨-378039999616,-378039999552⟩ : DyadicInterval 40),(⟨714906525043,714906544372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281495097728,281495097792⟩ : DyadicInterval 40),(⟨-379326420416,-379326420352⟩ : DyadicInterval 40),(⟨714632993934,714633013263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280541340608,280541340672⟩ : DyadicInterval 40),(⟨-377588926976,-377588926912⟩ : DyadicInterval 40),(⟨715002316447,715002335777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281495097728,281495097792⟩ : DyadicInterval 40),(⟨-379326420416,-379326420352⟩ : DyadicInterval 40),(⟨714632993934,714633013263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,171065651⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171052288,171052352⟩ : DyadicInterval 40),(⟨-171078976,-171078912⟩ : DyadicInterval 40),(⟨762123370280,762123389610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26624,0⟩ : DyadicInterval 40),(⟨762123383616,762123416192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨319739949026,320811517112⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨280665260672,280665260736⟩ : DyadicInterval 40),(⟨-377814436416,-377814436352⟩ : DyadicInterval 40),(⟨714954434264,714954453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281495104448,281495104512⟩ : DyadicInterval 40),(⟨-379326432704,-379326432640⟩ : DyadicInterval 40),(⟨714632991336,714633010666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-97831328256,-97149175616⟩ : DyadicInterval 40),(⟨810697971424,811039067008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨280789170944,281495097792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-379326420416,-378039999552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e183_ok : ecellOkT e183 = true := by decide +kernel
theorem e183_pos {a z : ℝ} (ha1 : ((29793/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((298779/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e183 e183_ok ha1 ha2 hz1 hz2 hz

-- box ['298779/1024000', '74907/256000', '999/1000', '1']  interval_lower 910436703/1099511627776
noncomputable def e184 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1420323136208,0,true,281495097728,281495097792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨778700119344,0,false,-379326420416,-379326420352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1421234743018,0,true,282200571520,282200571584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨777788512534,0,false,-380614348160,-380614348096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1420002324699,0,true,281246720512,281246720576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨779020930853,0,false,-378873533184,-378873533120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099683245406,0,true,171604224,171604288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099340010146,0,false,-171631040,-171630976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511600989,0,false,-26816,-26752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1420162727832,0,true,281370914112,281370914176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨778860527720,0,false,-379099949824,-379099949760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1421234751687,0,true,282200578240,282200578304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨777788503865,0,false,-380614360384,-380614360320⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1005373679759,0,false,-98413782144,-98413782080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1005999994639,0,false,-97729035648,-97729035584⟩
    { al := (298779/1024000), au := (74907/256000), zl := (999/1000), zu := 1,
      A := ⟨320811508432,321723115242⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281495097728,281495097792⟩ : DyadicInterval 40),(⟨-379326420416,-379326420352⟩ : DyadicInterval 40),(⟨714632993934,714633013264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282200571520,282200571584⟩ : DyadicInterval 40),(⟨-380614348160,-380614348096⟩ : DyadicInterval 40),(⟨714358636738,714358656067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281246720512,281246720576⟩ : DyadicInterval 40),(⟨-378873533184,-378873533120⟩ : DyadicInterval 40),(⟨714729348867,714729368197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282200571520,282200571584⟩ : DyadicInterval 40),(⟨-380614348160,-380614348096⟩ : DyadicInterval 40),(⟨714358636738,714358656067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,171617630⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171604224,171604288⟩ : DyadicInterval 40),(⟨-171631040,-171630976⟩ : DyadicInterval 40),(⟨762123370172,762123389502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26816,0⟩ : DyadicInterval 40),(⟨762123383616,762123416288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨320651100056,321723123911⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281370914112,281370914176⟩ : DyadicInterval 40),(⟨-379099949824,-379099949760⟩ : DyadicInterval 40),(⟨714681184986,714681204315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282200578240,282200578304⟩ : DyadicInterval 40),(⟨-380614360384,-380614360320⟩ : DyadicInterval 40),(⟨714358634105,714358653434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-98413782144,-97729035584⟩ : DyadicInterval 40),(⟨810987901408,811330293952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨281495097728,282200571584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-380614348160,-379326420352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e184_ok : ecellOkT e184 = true := by decide +kernel
theorem e184_pos {a z : ℝ} (ha1 : ((298779/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((74907/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e184 e184_ok ha1 ha2 hz1 hz2 hz

-- box ['74907/256000', '300477/1024000', '999/1000', '1']  interval_lower 968992017/1099511627776
noncomputable def e185 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1421234743017,0,true,282200571520,282200571584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨777788512535,0,false,-380614348160,-380614348096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1422146349827,0,true,282905592960,282905593024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨776876905725,0,false,-381903786240,-381903786176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1420913019901,0,true,281951648256,281951648320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨778110235651,0,false,-380159642048,-380159641984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099683798010,0,true,172156736,172156800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099339457542,0,false,-172183744,-172183680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511600816,0,false,-27008,-26944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1421073878860,0,true,282076114944,282076115008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨777949376692,0,false,-380386967936,-380386967872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1422146358498,0,true,282905599680,282905599744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨776876897054,0,false,-381903798464,-381903798400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1004839441654,0,false,-98998198784,-98998198720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1005467800763,0,false,-98310852928,-98310852864⟩
    { al := (74907/256000), au := (300477/1024000), zl := (999/1000), zu := 1,
      A := ⟨321723115241,322634722051⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282200571520,282200571584⟩ : DyadicInterval 40),(⟨-380614348160,-380614348096⟩ : DyadicInterval 40),(⟨714358636738,714358656067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282905592960,282905593024⟩ : DyadicInterval 40),(⟨-381903786240,-381903786176⟩ : DyadicInterval 40),(⟨714083452928,714083472258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨281951648256,281951648320⟩ : DyadicInterval 40),(⟨-380159642048,-380159641984⟩ : DyadicInterval 40),(⟨714455556908,714455576237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282905592960,282905593024⟩ : DyadicInterval 40),(⟨-381903786240,-381903786176⟩ : DyadicInterval 40),(⟨714083452928,714083472258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,172170234⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172156736,172156800⟩ : DyadicInterval 40),(⟨-172183744,-172183680⟩ : DyadicInterval 40),(⟨762123370096,762123389425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27008,0⟩ : DyadicInterval 40),(⟨762123383616,762123416384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨321562251084,322634730722⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282076114944,282076115008⟩ : DyadicInterval 40),(⟨-380386967936,-380386967872⟩ : DyadicInterval 40),(⟨714407110463,714407129792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282905599680,282905599744⟩ : DyadicInterval 40),(⟨-381903798464,-381903798400⟩ : DyadicInterval 40),(⟨714083450279,714083469609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-98998198784,-98310852864⟩ : DyadicInterval 40),(⟨811278810048,811622502272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨282200571520,282905593024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-381903786240,-380614348096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e185_ok : ecellOkT e185 = true := by decide +kernel
theorem e185_pos {a z : ℝ} (ha1 : ((74907/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((300477/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e185 e185_ok ha1 ha2 hz1 hz2 hz

-- box ['300477/1024000', '150663/512000', '999/1000', '1']  interval_lower 128538697/137438953472
noncomputable def e186 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1422146349826,0,true,282905592960,282905593024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨776876905726,0,false,-381903786240,-381903786176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1423057956635,0,true,283610162624,283610162688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨775965298917,0,false,-383194738240,-383194738176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1421823715103,0,true,282656124352,282656124416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨777199540449,0,false,-381447257024,-381447256960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099684351239,0,true,172709888,172709952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099338904313,0,false,-172737088,-172737024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511600642,0,false,-27136,-27072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1421985029895,0,true,282780863744,282780863808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨777038225657,0,false,-381675494272,-381675494208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1423057965311,0,true,283610169344,283610169408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨775965290241,0,false,-383194750528,-383194750464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1004303691918,0,false,-99584581184,-99584581120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1004934096764,0,false,-98894630528,-98894630464⟩
    { al := (300477/1024000), au := (150663/512000), zl := (999/1000), zu := 1,
      A := ⟨322634722050,323546328859⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282905592960,282905593024⟩ : DyadicInterval 40),(⟨-381903786240,-381903786176⟩ : DyadicInterval 40),(⟨714083452929,714083472258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨283610162624,283610162688⟩ : DyadicInterval 40),(⟨-383194738240,-383194738176⟩ : DyadicInterval 40),(⟨713807442083,713807461413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282656124352,282656124416⟩ : DyadicInterval 40),(⟨-381447257024,-381447256960⟩ : DyadicInterval 40),(⟨714180940154,714180959484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨283610162624,283610162688⟩ : DyadicInterval 40),(⟨-383194738240,-383194738176⟩ : DyadicInterval 40),(⟨713807442083,713807461413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,172723463⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172709888,172709952⟩ : DyadicInterval 40),(⟨-172737088,-172737024⟩ : DyadicInterval 40),(⟨762123370018,762123389347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27136,0⟩ : DyadicInterval 40),(⟨762123383616,762123416448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨322473402119,323546337535⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨282780863744,282780863808⟩ : DyadicInterval 40),(⟨-381675494272,-381675494208⟩ : DyadicInterval 40),(⟨714132210255,714132229585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨283610169344,283610169408⟩ : DyadicInterval 40),(⟨-383194750528,-383194750464⟩ : DyadicInterval 40),(⟨713807439439,713807458769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-99584581184,-98894630464⟩ : DyadicInterval 40),(⟨811570698848,811915693472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨282905592960,283610162688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-383194738240,-381903786176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e186_ok : ecellOkT e186 = true := by decide +kernel
theorem e186_pos {a z : ℝ} (ha1 : ((300477/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((150663/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e186 e186_ok ha1 ha2 hz1 hz2 hz

-- box ['150663/512000', '12087/40960', '999/1000', '1']  interval_lower 544197591/549755813888
noncomputable def e187 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1423057956634,0,true,283610162624,283610162688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨775965298918,0,false,-383194738240,-383194738176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1423969563444,0,true,284314281088,284314281152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨775053692108,0,false,-384487207808,-384487207744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1422734410305,0,true,283360149312,283360149376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨776288845247,0,false,-382736381632,-382736381568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099684905097,0,true,173263616,173263680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099338350455,0,false,-173291008,-173290944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511600468,0,false,-27328,-27264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1422896180928,0,true,283485161088,283485161152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨776127074624,0,false,-382965532480,-382965532416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1423969572118,0,true,284314287744,284314287808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨775053683434,0,false,-384487220096,-384487220032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1003766430556,0,false,-100172932288,-100172932224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1004398882649,0,false,-99480371328,-99480371264⟩
    { al := (150663/512000), au := (12087/40960), zl := (999/1000), zu := 1,
      A := ⟨323546328858,324457935668⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨283610162624,283610162688⟩ : DyadicInterval 40),(⟨-383194738240,-383194738176⟩ : DyadicInterval 40),(⟨713807442083,713807461413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284314281088,284314281152⟩ : DyadicInterval 40),(⟨-384487207808,-384487207744⟩ : DyadicInterval 40),(⟨713530603792,713530623122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨283360149312,283360149376⟩ : DyadicInterval 40),(⟨-382736381632,-382736381568⟩ : DyadicInterval 40),(⟨713905498207,713905517537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284314281088,284314281152⟩ : DyadicInterval 40),(⟨-384487207808,-384487207744⟩ : DyadicInterval 40),(⟨713530603792,713530623122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,173277321⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173263616,173263680⟩ : DyadicInterval 40),(⟨-173291008,-173290944⟩ : DyadicInterval 40),(⟨762123369940,762123389269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27328,0⟩ : DyadicInterval 40),(⟨762123383616,762123416544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨323384553152,324457944342⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨283485161088,283485161152⟩ : DyadicInterval 40),(⟨-382965532480,-382965532416⟩ : DyadicInterval 40),(⟨713856483969,713856503298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284314287744,284314287808⟩ : DyadicInterval 40),(⟨-384487220096,-384487220032⟩ : DyadicInterval 40),(⟨713530601175,713530620505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-100172932288,-99480371264⟩ : DyadicInterval 40),(⟨811863569248,812209869024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨283610162624,284314281152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-384487207808,-383194738176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e187_ok : ecellOkT e187 = true := by decide +kernel
theorem e187_pos {a z : ℝ} (ha1 : ((150663/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((12087/40960 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e187 e187_ok ha1 ha2 hz1 hz2 hz

-- box ['12087/40960', '18939/64000', '999/1000', '1']  interval_lower 1149255719/1099511627776
noncomputable def e188 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1423969563443,0,true,284314281088,284314281152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨775053692109,0,false,-384487207808,-384487207744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1424881170252,0,true,285017948928,285017948992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨774142085300,0,false,-385781198400,-385781198336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1423645105507,0,true,284063723776,284063723840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨775378150045,0,false,-384027019520,-384027019456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099685459588,0,true,173818048,173818112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099337795964,0,false,-173845568,-173845504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511600293,0,false,-27520,-27456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1423807331954,0,true,284189007616,284189007680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨775215923598,0,false,-384257086016,-384257085952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1424881178932,0,true,285017955584,285017955648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨774142076620,0,false,-385781210752,-385781210688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1003227657561,0,false,-100763255104,-100763255040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1003862158420,0,false,-100068078336,-100068078272⟩
    { al := (12087/40960), au := (18939/64000), zl := (999/1000), zu := 1,
      A := ⟨324457935667,325369542476⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284314281088,284314281152⟩ : DyadicInterval 40),(⟨-384487207808,-384487207744⟩ : DyadicInterval 40),(⟨713530603793,713530623122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285017948928,285017948992⟩ : DyadicInterval 40),(⟨-385781198400,-385781198336⟩ : DyadicInterval 40),(⟨713252937574,713252956904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284063723776,284063723840⟩ : DyadicInterval 40),(⟨-384027019520,-384027019456⟩ : DyadicInterval 40),(⟨713629230625,713629249955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285017948928,285017948992⟩ : DyadicInterval 40),(⟨-385781198400,-385781198336⟩ : DyadicInterval 40),(⟨713252937574,713252956904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,173831812⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173818048,173818112⟩ : DyadicInterval 40),(⟨-173845568,-173845504⟩ : DyadicInterval 40),(⟨762123369829,762123389158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27520,0⟩ : DyadicInterval 40),(⟨762123383616,762123416640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨324295704178,325369551156⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284189007616,284189007680⟩ : DyadicInterval 40),(⟨-384257086016,-384257085952⟩ : DyadicInterval 40),(⟨713579931089,713579950419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285017955584,285017955648⟩ : DyadicInterval 40),(⟨-385781210752,-385781210688⟩ : DyadicInterval 40),(⟨713252934962,713252954291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-100763255104,-100068078272⟩ : DyadicInterval 40),(⟨812157422752,812505030432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨284314281088,285017948992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-385781198400,-384487207744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e188_ok : ecellOkT e188 = true := by decide +kernel
theorem e188_pos {a z : ℝ} (ha1 : ((12087/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((18939/64000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e188 e188_ok ha1 ha2 hz1 hz2 hz

-- box ['18939/64000', '303873/1024000', '999/1000', '1']  interval_lower 1210898287/1099511627776
noncomputable def e189 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1424881170251,0,true,285017948928,285017948992⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨774142085301,0,false,-385781198400,-385781198336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1425792777061,0,true,285721166720,285721166784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨773230478491,0,false,-387076713664,-387076713600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1424555800708,0,true,284766848384,284766848448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨774467454844,0,false,-385319174144,-385319174080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099686014711,0,true,174373056,174373120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099337240841,0,false,-174400768,-174400704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511600117,0,false,-27712,-27648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1424718482994,0,true,284892403904,284892403968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨774304772558,0,false,-385550158464,-385550158400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1425792785744,0,true,285721173376,285721173440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨773230469808,0,false,-387076726016,-387076725952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1002687372938,0,false,-101355552576,-101355552512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1003323924064,0,false,-100657754560,-100657754496⟩
    { al := (18939/64000), au := (303873/1024000), zl := (999/1000), zu := 1,
      A := ⟨325369542475,326281149285⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285017948928,285017948992⟩ : DyadicInterval 40),(⟨-385781198400,-385781198336⟩ : DyadicInterval 40),(⟨713252937574,713252956904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285721166720,285721166784⟩ : DyadicInterval 40),(⟨-387076713664,-387076713600⟩ : DyadicInterval 40),(⟨712974443007,712974462336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284766848384,284766848448⟩ : DyadicInterval 40),(⟨-385319174144,-385319174080⟩ : DyadicInterval 40),(⟨713352136889,713352156218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285721166720,285721166784⟩ : DyadicInterval 40),(⟨-387076713664,-387076713600⟩ : DyadicInterval 40),(⟨712974443007,712974462336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,174386935⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174373056,174373120⟩ : DyadicInterval 40),(⟨-174400768,-174400704⟩ : DyadicInterval 40),(⟨762123369749,762123389078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27712,0⟩ : DyadicInterval 40),(⟨762123383616,762123416736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨325206855218,326281157968⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨284892403904,284892403968⟩ : DyadicInterval 40),(⟨-385550158464,-385550158400⟩ : DyadicInterval 40),(⟨713302551176,713302570506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285721173376,285721173440⟩ : DyadicInterval 40),(⟨-387076726016,-387076725952⟩ : DyadicInterval 40),(⟨712974440378,712974459707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-101355552576,-100657754496⟩ : DyadicInterval 40),(⟨812452260864,812801179168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨285017948928,285721166784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-387076713664,-385781198336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e189_ok : ecellOkT e189 = true := by decide +kernel
theorem e189_pos {a z : ℝ} (ha1 : ((18939/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((303873/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e189 e189_ok ha1 ha2 hz1 hz2 hz

-- box ['303873/1024000', '152361/512000', '999/1000', '1']  interval_lower 79583053/68719476736
noncomputable def e190 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1425792777060,0,true,285721166720,285721166784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨773230478492,0,false,-387076713664,-387076713600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1426704383869,0,true,286423935040,286423935104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨772318871683,0,false,-388373757248,-388373757184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1425466495910,0,true,285469523584,285469523648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨773556759642,0,false,-386612849088,-386612849024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099686570474,0,true,174928768,174928832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099336685078,0,false,-174956672,-174956608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511599940,0,false,-27840,-27776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1425629634030,0,true,285595350464,285595350528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨773393621522,0,false,-386844753472,-386844753344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1426704392547,0,true,286423941696,286423941760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨772318863005,0,false,-388373769600,-388373769536⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1002145576691,0,false,-101949827840,-101949827776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1002784179593,0,false,-101249402944,-101249402880⟩
    { al := (303873/1024000), au := (152361/512000), zl := (999/1000), zu := 1,
      A := ⟨326281149284,327192756093⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285721166720,285721166784⟩ : DyadicInterval 40),(⟨-387076713664,-387076713600⟩ : DyadicInterval 40),(⟨712974443007,712974462336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286423935040,286423935104⟩ : DyadicInterval 40),(⟨-388373757248,-388373757184⟩ : DyadicInterval 40),(⟨712695119660,712695138990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285469523584,285469523648⟩ : DyadicInterval 40),(⟨-386612849088,-386612849024⟩ : DyadicInterval 40),(⟨713074216643,713074235973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286423935040,286423935104⟩ : DyadicInterval 40),(⟨-388373757248,-388373757184⟩ : DyadicInterval 40),(⟨712695119660,712695138990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,174942698⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174928768,174928832⟩ : DyadicInterval 40),(⟨-174956672,-174956608⟩ : DyadicInterval 40),(⟨762123369668,762123388998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27840,0⟩ : DyadicInterval 40),(⟨762123383616,762123416800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨326118006254,327192764771⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨285595350464,285595350528⟩ : DyadicInterval 40),(⟨-386844753472,-386844753344⟩ : DyadicInterval 40),(⟨713024343837,713024363189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286423941696,286423941760⟩ : DyadicInterval 40),(⟨-388373769600,-388373769536⟩ : DyadicInterval 40),(⟨712695117017,712695136347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-101949827840,-101249402880⟩ : DyadicInterval 40),(⟨812748085056,813098316800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨285721166720,286423935104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-388373757248,-387076713600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e190_ok : ecellOkT e190 = true := by decide +kernel
theorem e190_pos {a z : ℝ} (ha1 : ((303873/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((152361/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e190 e190_ok ha1 ha2 hz1 hz2 hz

-- box ['152361/512000', '305571/1024000', '999/1000', '1']  interval_lower 668277103/549755813888
noncomputable def e191 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1426704383868,0,true,286423935040,286423935104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨772318871684,0,false,-388373757248,-388373757184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1427615990678,0,true,287126254464,287126254528⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨771407264874,0,false,-389672332672,-389672332608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1426377191111,0,true,286171750016,286171750080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨772646064441,0,false,-387908047936,-387908047872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099687126875,0,true,175485056,175485120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099336128677,0,false,-175513152,-175513088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511599763,0,false,-28032,-27968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1426540785062,0,true,286297847872,286297847936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨772482470490,0,false,-388140874496,-388140874432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1427615999356,0,true,287126261120,287126261184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨771407256196,0,false,-389672345024,-389672344960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1001602268811,0,false,-102546083840,-102546083776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1002242925006,0,false,-101843026560,-101843026496⟩
    { al := (152361/512000), au := (305571/1024000), zl := (999/1000), zu := 1,
      A := ⟨327192756092,328104362902⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286423935040,286423935104⟩ : DyadicInterval 40),(⟨-388373757248,-388373757184⟩ : DyadicInterval 40),(⟨712695119661,712695138990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287126254464,287126254528⟩ : DyadicInterval 40),(⟨-389672332672,-389672332608⟩ : DyadicInterval 40),(⟨712414967055,712414986384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286171750016,286171750080⟩ : DyadicInterval 40),(⟨-387908047936,-387908047872⟩ : DyadicInterval 40),(⟨712795469403,712795488732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287126254464,287126254528⟩ : DyadicInterval 40),(⟨-389672332672,-389672332608⟩ : DyadicInterval 40),(⟨712414967055,712414986384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,175499099⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨175485056,175485120⟩ : DyadicInterval 40),(⟨-175513152,-175513088⟩ : DyadicInterval 40),(⟨762123369587,762123388916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28032,0⟩ : DyadicInterval 40),(⟨762123383616,762123416896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨327029157286,328104371580⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286297847872,286297847936⟩ : DyadicInterval 40),(⟨-388140874496,-388140874432⟩ : DyadicInterval 40),(⟨712745308644,712745327973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287126261120,287126261184⟩ : DyadicInterval 40),(⟨-389672345024,-389672344960⟩ : DyadicInterval 40),(⟨712414964396,712414983725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-102546083840,-101843026496⟩ : DyadicInterval 40),(⟨813044896864,813396444800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨286423935040,287126254528⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-389672332672,-388373757184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e191_ok : ecellOkT e191 = true := by decide +kernel
theorem e191_pos {a z : ℝ} (ha1 : ((152361/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((305571/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e191 e191_ok ha1 ha2 hz1 hz2 hz

-- box ['305571/1024000', '15321/51200', '999/1000', '1']  interval_lower 43768161/34359738368
noncomputable def e192 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1427615990677,0,true,287126254464,287126254528⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨771407264875,0,false,-389672332672,-389672332608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1428527597487,0,true,287828125568,287828125632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨770495658065,0,false,-390972443584,-390972443520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1427287886314,0,true,286873528192,286873528256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨771735369238,0,false,-389204774336,-389204774272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099687683920,0,true,176042048,176042112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099335571632,0,false,-176070272,-176070208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511599585,0,false,-28224,-28160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1427451936089,0,true,286999896768,286999896832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨771571319463,0,false,-389438525248,-389438525184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1428527606166,0,true,287828132224,287828132288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨770495649386,0,false,-390972455936,-390972455872⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1001057449301,0,false,-103144323648,-103144323584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1001700160303,0,false,-102438628480,-102438628416⟩
    { al := (305571/1024000), au := (15321/51200), zl := (999/1000), zu := 1,
      A := ⟨328104362901,329015969711⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287126254464,287126254528⟩ : DyadicInterval 40),(⟨-389672332672,-389672332608⟩ : DyadicInterval 40),(⟨712414967055,712414986384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287828125568,287828125632⟩ : DyadicInterval 40),(⟨-390972443584,-390972443520⟩ : DyadicInterval 40),(⟨712133984747,712134004076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286873528192,286873528256⟩ : DyadicInterval 40),(⟨-389204774336,-389204774272⟩ : DyadicInterval 40),(⟨712515894778,712515914108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287828125568,287828125632⟩ : DyadicInterval 40),(⟨-390972443584,-390972443520⟩ : DyadicInterval 40),(⟨712133984747,712134004076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,176056144⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176042048,176042112⟩ : DyadicInterval 40),(⟨-176070272,-176070208⟩ : DyadicInterval 40),(⟨762123369473,762123388802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28224,0⟩ : DyadicInterval 40),(⟨762123383616,762123416992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨327940308313,329015978390⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨286999896768,286999896832⟩ : DyadicInterval 40),(⟨-389438525248,-389438525184⟩ : DyadicInterval 40),(⟨712465445079,712465464409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287828132224,287828132288⟩ : DyadicInterval 40),(⟨-390972455936,-390972455872⟩ : DyadicInterval 40),(⟨712133982072,712134001401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-103144323648,-102438628416⟩ : DyadicInterval 40),(⟨813342697824,813695564704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨287126254464,287828125632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-390972443584,-389672332608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e192_ok : ecellOkT e192 = true := by decide +kernel
theorem e192_pos {a z : ℝ} (ha1 : ((305571/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((15321/51200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e192 e192_ok ha1 ha2 hz1 hz2 hz

-- box ['15321/51200', '307269/1024000', '999/1000', '1']  interval_lower 1465416335/1099511627776
noncomputable def e193 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1428527597486,0,true,287828125568,287828125632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨770495658066,0,false,-390972443584,-390972443520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1429439204295,0,true,288529548928,288529548992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨769584051257,0,false,-392274093568,-392274093504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1428198581516,0,true,287574858816,287574858880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨770824674036,0,false,-390503031872,-390503031808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099688241611,0,true,176599616,176599680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099335013941,0,false,-176628032,-176627968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511599406,0,false,-28416,-28352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1428363087127,0,true,287701497664,287701497728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨770660168425,0,false,-390737709248,-390737709184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1429439212987,0,true,288529555584,288529555648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨769584042565,0,false,-392274105984,-392274105920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1000511118155,0,false,-103744550400,-103744550336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1001155885477,0,false,-103036211584,-103036211520⟩
    { al := (15321/51200), au := (307269/1024000), zl := (999/1000), zu := 1,
      A := ⟨329015969710,329927576519⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287828125568,287828125632⟩ : DyadicInterval 40),(⟨-390972443584,-390972443520⟩ : DyadicInterval 40),(⟨712133984747,712134004076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288529548928,288529548992⟩ : DyadicInterval 40),(⟨-392274093568,-392274093504⟩ : DyadicInterval 40),(⟨711852172264,711852191594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287574858816,287574858880⟩ : DyadicInterval 40),(⟨-390503031872,-390503031808⟩ : DyadicInterval 40),(⟨712235492229,712235511558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288529548928,288529548992⟩ : DyadicInterval 40),(⟨-392274093568,-392274093504⟩ : DyadicInterval 40),(⟨711852172264,711852191594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,176613835⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176599616,176599680⟩ : DyadicInterval 40),(⟨-176628032,-176627968⟩ : DyadicInterval 40),(⟨762123369390,762123388719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28416,0⟩ : DyadicInterval 40),(⟨762123383616,762123417088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨328851459351,329927585211⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨287701497664,287701497728⟩ : DyadicInterval 40),(⟨-390737709248,-390737709184⟩ : DyadicInterval 40),(⟨712184752717,712184772047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288529555584,288529555648⟩ : DyadicInterval 40),(⟨-392274105984,-392274105920⟩ : DyadicInterval 40),(⟨711852169592,711852188922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-103744550400,-103036211520⟩ : DyadicInterval 40),(⟨813641489376,813995678080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨287828125568,288529548992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-392274093568,-390972443520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e193_ok : ecellOkT e193 = true := by decide +kernel
theorem e193_pos {a z : ℝ} (ha1 : ((15321/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((307269/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e193 e193_ok ha1 ha2 hz1 hz2 hz

-- box ['307269/1024000', '154059/512000', '999/1000', '1']  interval_lower 1531066835/1099511627776
noncomputable def e194 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1429439204294,0,true,288529548928,288529548992⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨769584051258,0,false,-392274093568,-392274093504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1430350811104,0,true,289230525056,289230525120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨768672444448,0,false,-393577286400,-393577286336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1429109276717,0,true,288275742336,288275742400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨769913978835,0,false,-391802824128,-391802824064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099688799949,0,true,177157888,177157952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099334455603,0,false,-177186496,-177186432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511599226,0,false,-28608,-28544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1429274238164,0,true,288402651136,288402651200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨769749017388,0,false,-392038430272,-392038430208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1430350819783,0,true,289230531712,289230531776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨768672435769,0,false,-393577298816,-393577298752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨999963275395,0,false,-104346767040,-104346766976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1000610100532,0,false,-103635779072,-103635779008⟩
    { al := (307269/1024000), au := (154059/512000), zl := (999/1000), zu := 1,
      A := ⟨329927576518,330839183328⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288529548928,288529548992⟩ : DyadicInterval 40),(⟨-392274093568,-392274093504⟩ : DyadicInterval 40),(⟨711852172265,711852191595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289230525056,289230525120⟩ : DyadicInterval 40),(⟨-393577286400,-393577286336⟩ : DyadicInterval 40),(⟨711569529238,711569548567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288275742336,288275742400⟩ : DyadicInterval 40),(⟨-391802824128,-391802824064⟩ : DyadicInterval 40),(⟨711954261372,711954280702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289230525056,289230525120⟩ : DyadicInterval 40),(⟨-393577286400,-393577286336⟩ : DyadicInterval 40),(⟨711569529238,711569548567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,177172173⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177157888,177157952⟩ : DyadicInterval 40),(⟨-177186496,-177186432⟩ : DyadicInterval 40),(⟨762123369306,762123388636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28608,0⟩ : DyadicInterval 40),(⟨762123383616,762123417184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨329762610388,330839192007⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288402651136,288402651200⟩ : DyadicInterval 40),(⟨-392038430272,-392038430208⟩ : DyadicInterval 40),(⟨711903231160,711903250489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289230531712,289230531776⟩ : DyadicInterval 40),(⟨-393577298816,-393577298752⟩ : DyadicInterval 40),(⟨711569526553,711569545883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-104346767040,-103635779008⟩ : DyadicInterval 40),(⟨813941273120,814296786400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨288529548928,289230525120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-393577286400,-392274093504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e194_ok : ecellOkT e194 = true := by decide +kernel
theorem e194_pos {a z : ℝ} (ha1 : ((307269/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154059/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e194 e194_ok ha1 ha2 hz1 hz2 hz

-- box ['154059/512000', '308967/1024000', '999/1000', '1']  interval_lower 798769717/549755813888
noncomputable def e195 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1430350811103,0,true,289230525056,289230525120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨768672444449,0,false,-393577286400,-393577286336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1431262417912,0,true,289931054592,289931054656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨767760837640,0,false,-394882025664,-394882025600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1430019971919,0,true,288976179328,288976179392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨769003283633,0,false,-393104154752,-393104154688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099689358940,0,true,177716800,177716864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099333896612,0,false,-177745536,-177745472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511599046,0,false,-28736,-28672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1430185389189,0,true,289103357760,289103357824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨768837866363,0,false,-393340691776,-393340691712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1431262426586,0,true,289931061312,289931061376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨767760828966,0,false,-394882038080,-394882038016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨999413921002,0,false,-104950976768,-104950976704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1000062805477,0,false,-104237334016,-104237333952⟩
    { al := (154059/512000), au := (308967/1024000), zl := (999/1000), zu := 1,
      A := ⟨330839183327,331750790136⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289230525056,289230525120⟩ : DyadicInterval 40),(⟨-393577286400,-393577286336⟩ : DyadicInterval 40),(⟨711569529238,711569548567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289931054592,289931054656⟩ : DyadicInterval 40),(⟨-394882025664,-394882025600⟩ : DyadicInterval 40),(⟨711286055138,711286074468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨288976179328,288976179392⟩ : DyadicInterval 40),(⟨-393104154752,-393104154688⟩ : DyadicInterval 40),(⟨711672201758,711672221087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289931054592,289931054656⟩ : DyadicInterval 40),(⟨-394882025664,-394882025600⟩ : DyadicInterval 40),(⟨711286055138,711286074468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,177731164⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177716800,177716864⟩ : DyadicInterval 40),(⟨-177745536,-177745472⟩ : DyadicInterval 40),(⟨762123369190,762123388519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28736,0⟩ : DyadicInterval 40),(⟨762123383616,762123417248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨330673761413,331750798810⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289103357760,289103357824⟩ : DyadicInterval 40),(⟨-393340691776,-393340691712⟩ : DyadicInterval 40),(⟨711620879890,711620899219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289931061312,289931061376⟩ : DyadicInterval 40),(⟨-394882038080,-394882038016⟩ : DyadicInterval 40),(⟨711286052398,711286071727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-104950976768,-104237333952⟩ : DyadicInterval 40),(⟨814242050592,814598891264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨289230525056,289931054656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-394882025664,-393577286336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e195_ok : ecellOkT e195 = true := by decide +kernel
theorem e195_pos {a z : ℝ} (ha1 : ((154059/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308967/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e195 e195_ok ha1 ha2 hz1 hz2 hz

-- box ['308967/1024000', '38727/128000', '999/1000', '1']  interval_lower 104052545/68719476736
noncomputable def e196 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1431262417911,0,true,289931054592,289931054656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨767760837641,0,false,-394882025664,-394882025600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1432174024721,0,true,290631138112,290631138176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨766849230831,0,false,-396188315008,-396188314944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1430930667120,0,true,289676170432,289676170496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨768092588432,0,false,-394407027392,-394407027328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099689918584,0,true,178276352,178276416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099333336968,0,false,-178305280,-178305216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511598865,0,false,-28928,-28864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1431096540219,0,true,289803618176,289803618240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨767926715333,0,false,-394644497600,-394644497536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1432174033401,0,true,290631144768,290631144832⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨766849222151,0,false,-396188327488,-396188327424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨998863054972,0,false,-105557182656,-105557182592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨999514000301,0,false,-104840879360,-104840879296⟩
    { al := (308967/1024000), au := (38727/128000), zl := (999/1000), zu := 1,
      A := ⟨331750790135,332662396945⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289931054592,289931054656⟩ : DyadicInterval 40),(⟨-394882025664,-394882025600⟩ : DyadicInterval 40),(⟨711286055138,711286074468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨290631138112,290631138176⟩ : DyadicInterval 40),(⟨-396188315008,-396188314944⟩ : DyadicInterval 40),(⟨711001749495,711001768825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289676170432,289676170496⟩ : DyadicInterval 40),(⟨-394407027392,-394407027328⟩ : DyadicInterval 40),(⟨711389312887,711389332216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨290631138112,290631138176⟩ : DyadicInterval 40),(⟨-396188315008,-396188314944⟩ : DyadicInterval 40),(⟨711001749495,711001768825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,178290808⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178276352,178276416⟩ : DyadicInterval 40),(⟨-178305280,-178305216⟩ : DyadicInterval 40),(⟨762123369104,762123388434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28928,0⟩ : DyadicInterval 40),(⟨762123383616,762123417344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨331584912443,332662405625⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨289803618176,289803618240⟩ : DyadicInterval 40),(⟨-394644497600,-394644497536⟩ : DyadicInterval 40),(⟨711337698467,711337717797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨290631144768,290631144832⟩ : DyadicInterval 40),(⟨-396188327488,-396188327424⟩ : DyadicInterval 40),(⟨711001746802,711001766131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-105557182656,-104840879296⟩ : DyadicInterval 40),(⟨814543823264,814901994208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨289931054592,290631138176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-396188315008,-394882025600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e196_ok : ecellOkT e196 = true := by decide +kernel
theorem e196_pos {a z : ℝ} (ha1 : ((308967/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((38727/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e196 e196_ok ha1 ha2 hz1 hz2 hz

-- box ['38727/128000', '62133/204800', '999/1000', '1']  interval_lower 866489019/549755813888
noncomputable def e197 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1432174024720,0,true,290631138112,290631138176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨766849230832,0,false,-396188315008,-396188314944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1433085631529,0,true,291330776192,291330776256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨765937624023,0,false,-397496158144,-397496158080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1431841362322,0,true,290375716224,290375716288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨767181893230,0,false,-395711445696,-395711445632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099690478886,0,true,178836544,178836608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099332776666,0,false,-178865664,-178865600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511598683,0,false,-29120,-29056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1432007691264,0,true,290503432832,290503432896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨767015564288,0,false,-395949851264,-395949851200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1433085640225,0,true,291330782848,291330782912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨765937615327,0,false,-397496170688,-397496170624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨998310677308,0,false,-106165387776,-106165387712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨998963684997,0,false,-105446418368,-105446418304⟩
    { al := (38727/128000), au := (62133/204800), zl := (999/1000), zu := 1,
      A := ⟨332662396944,333574003753⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨290631138112,290631138176⟩ : DyadicInterval 40),(⟨-396188315008,-396188314944⟩ : DyadicInterval 40),(⟨711001749496,711001768825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291330776192,291330776256⟩ : DyadicInterval 40),(⟨-397496158144,-397496158080⟩ : DyadicInterval 40),(⟨710716611853,710716631183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨290375716224,290375716288⟩ : DyadicInterval 40),(⟨-395711445696,-395711445632⟩ : DyadicInterval 40),(⟨711105594295,711105613624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291330776192,291330776256⟩ : DyadicInterval 40),(⟨-397496158144,-397496158080⟩ : DyadicInterval 40),(⟨710716611853,710716631183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,178851110⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178836544,178836608⟩ : DyadicInterval 40),(⟨-178865664,-178865600⟩ : DyadicInterval 40),(⟨762123369018,762123388348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29120,0⟩ : DyadicInterval 40),(⟨762123383616,762123417440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨332496063488,333574012449⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨290503432832,290503432896⟩ : DyadicInterval 40),(⟨-395949851264,-395949851200⟩ : DyadicInterval 40),(⟨711053686460,711053705790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291330782848,291330782912⟩ : DyadicInterval 40),(⟨-397496170688,-397496170624⟩ : DyadicInterval 40),(⟨710716609161,710716628491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-106165387776,-105446418304⟩ : DyadicInterval 40),(⟨814846592768,815206096768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨290631138112,291330776256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-397496158144,-396188314944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e197_ok : ecellOkT e197 = true := by decide +kernel
theorem e197_pos {a z : ℝ} (ha1 : ((38727/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62133/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e197 e197_ok ha1 ha2 hz1 hz2 hz

-- box ['62133/204800', '155757/512000', '999/1000', '1']  interval_lower 56311209/34359738368
noncomputable def e198 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1433085631528,0,true,291330776192,291330776256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨765937624024,0,false,-397496158144,-397496158080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1433997238338,0,true,292029969280,292029969344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨765026017214,0,false,-398805558848,-398805558784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1432752057524,0,true,291074817152,291074817216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨766271198028,0,false,-397017413376,-397017413312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099691039848,0,true,179397376,179397440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099332215704,0,false,-179426752,-179426688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511598500,0,false,-29312,-29248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1432918842303,0,true,291202802368,291202802432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨766104413249,0,false,-397256756544,-397256756480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1433997247019,0,true,292029975936,292029976000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨765026008533,0,false,-398805571328,-398805571264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨997756788032,0,false,-106775595328,-106775595264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨998411859579,0,false,-106053954112,-106053954048⟩
    { al := (62133/204800), au := (155757/512000), zl := (999/1000), zu := 1,
      A := ⟨333574003752,334485610562⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291330776192,291330776256⟩ : DyadicInterval 40),(⟨-397496158144,-397496158080⟩ : DyadicInterval 40),(⟨710716611854,710716631183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292029969280,292029969344⟩ : DyadicInterval 40),(⟨-398805558848,-398805558784⟩ : DyadicInterval 40),(⟨710430641856,710430661186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291074817152,291074817216⟩ : DyadicInterval 40),(⟨-397017413376,-397017413312⟩ : DyadicInterval 40),(⟨710821045617,710821064946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292029969280,292029969344⟩ : DyadicInterval 40),(⟨-398805558848,-398805558784⟩ : DyadicInterval 40),(⟨710430641856,710430661186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,179412072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179397376,179397440⟩ : DyadicInterval 40),(⟨-179426752,-179426688⟩ : DyadicInterval 40),(⟨762123368964,762123388293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29312,0⟩ : DyadicInterval 40),(⟨762123383616,762123417536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨333407214527,334485619243⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291202802368,291202802432⟩ : DyadicInterval 40),(⟨-397256756544,-397256756480⟩ : DyadicInterval 40),(⟨710768843403,710768862733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292029975936,292029976000⟩ : DyadicInterval 40),(⟨-398805571328,-398805571264⟩ : DyadicInterval 40),(⟨710430639130,710430658460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-106775595328,-106053954048⟩ : DyadicInterval 40),(⟨815150360640,815511200544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨291330776192,292029969344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-398805558848,-397496158080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e198_ok : ecellOkT e198 = true := by decide +kernel
theorem e198_pos {a z : ℝ} (ha1 : ((62133/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((155757/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e198 e198_ok ha1 ha2 hz1 hz2 hz

-- box ['155757/512000', '312363/1024000', '999/1000', '1']  interval_lower 935894447/549755813888
noncomputable def e199 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1433997238337,0,true,292029969280,292029969344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨765026017215,0,false,-398805558848,-398805558784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1434908845147,0,true,292728718080,292728718144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨764114410405,0,false,-400116520704,-400116520640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1433662752726,0,true,291773473856,291773473920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨765360502826,0,false,-398324934080,-398324934016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099691601472,0,true,179958912,179958976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099331654080,0,false,-179988480,-179988416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511598316,0,false,-29504,-29440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1433829993327,0,true,291901727360,291901727424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨765193262225,0,false,-398565217024,-398565216960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1434908853837,0,true,292728724736,292728724800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨764114401715,0,false,-400116533248,-400116533184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨997201387113,0,false,-107387808448,-107387808384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨997858524052,0,false,-106663489600,-106663489536⟩
    { al := (155757/512000), au := (312363/1024000), zl := (999/1000), zu := 1,
      A := ⟨334485610561,335397217371⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292029969280,292029969344⟩ : DyadicInterval 40),(⟨-398805558848,-398805558784⟩ : DyadicInterval 40),(⟨710430641856,710430661186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292728718080,292728718144⟩ : DyadicInterval 40),(⟨-400116520704,-400116520640⟩ : DyadicInterval 40),(⟨710143838905,710143858234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291773473856,291773473920⟩ : DyadicInterval 40),(⟨-398324934080,-398324934016⟩ : DyadicInterval 40),(⟨710535666332,710535685662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292728718080,292728718144⟩ : DyadicInterval 40),(⟨-400116520704,-400116520640⟩ : DyadicInterval 40),(⟨710143838905,710143858234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,179973696⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179958912,179958976⟩ : DyadicInterval 40),(⟨-179988480,-179988416⟩ : DyadicInterval 40),(⟨762123368876,762123388206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29504,0⟩ : DyadicInterval 40),(⟨762123383616,762123417632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨334318365551,335397226061⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨291901727360,291901727424⟩ : DyadicInterval 40),(⟨-398565217024,-398565216960⟩ : DyadicInterval 40),(⟨710483168796,710483188125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292728724736,292728724800⟩ : DyadicInterval 40),(⟨-400116533248,-400116533184⟩ : DyadicInterval 40),(⟨710143836182,710143855512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-107387808448,-106663489536⟩ : DyadicInterval 40),(⟨815455128384,815817307104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨292029969280,292728718144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-400116520704,-398805558784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e199_ok : ecellOkT e199 = true := by decide +kernel
theorem e199_pos {a z : ℝ} (ha1 : ((155757/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((312363/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e199 e199_ok ha1 ha2 hz1 hz2 hz

-- box ['312363/1024000', '78303/256000', '999/1000', '1']  interval_lower 1942476509/1099511627776
noncomputable def e200 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1434908845146,0,true,292728718080,292728718144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨764114410406,0,false,-400116520704,-400116520640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1435820451955,0,true,293427023104,293427023168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨763202803597,0,false,-401429047552,-401429047488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1434573447928,0,true,292471686976,292471687040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨764449807624,0,false,-399634011520,-399634011456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099692163763,0,true,180521152,180521216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099331091789,0,false,-180550848,-180550784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511598132,0,false,-29696,-29632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1434741144374,0,true,292600208384,292600208448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨764282111178,0,false,-399875236544,-399875236480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1435820460647,0,true,293427029760,293427029824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨763202794905,0,false,-401429060096,-401429059968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨996644474569,0,false,-108002030272,-108002030208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨997303678393,0,false,-107275028160,-107275028096⟩
    { al := (312363/1024000), au := (78303/256000), zl := (999/1000), zu := 1,
      A := ⟨335397217370,336308824179⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292728718080,292728718144⟩ : DyadicInterval 40),(⟨-400116520704,-400116520640⟩ : DyadicInterval 40),(⟨710143838905,710143858235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293427023104,293427023168⟩ : DyadicInterval 40),(⟨-401429047552,-401429047488⟩ : DyadicInterval 40),(⟨709856202610,709856221940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292471686976,292471687040⟩ : DyadicInterval 40),(⟨-399634011520,-399634011456⟩ : DyadicInterval 40),(⟨710249455937,710249475267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293427023104,293427023168⟩ : DyadicInterval 40),(⟨-401429047552,-401429047488⟩ : DyadicInterval 40),(⟨709856202610,709856221940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,180535987⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180521152,180521216⟩ : DyadicInterval 40),(⟨-180550848,-180550784⟩ : DyadicInterval 40),(⟨762123368756,762123388086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29696,0⟩ : DyadicInterval 40),(⟨762123383616,762123417728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨335229516598,336308832871⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨292600208384,292600208448⟩ : DyadicInterval 40),(⟨-399875236544,-399875236480⟩ : DyadicInterval 40),(⟨710196662204,710196681534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293427029760,293427029824⟩ : DyadicInterval 40),(⟨-401429060096,-401429059968⟩ : DyadicInterval 40),(⟨709856199849,709856219200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-108002030272,-107275028096⟩ : DyadicInterval 40),(⟨815760897664,816124418016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨292728718080,293427023168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-401429047552,-400116520640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e200_ok : ecellOkT e200 = true := by decide +kernel
theorem e200_pos {a z : ℝ} (ha1 : ((312363/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((78303/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e200 e200_ok ha1 ha2 hz1 hz2 hz

-- box ['78303/256000', '314061/1024000', '999/1000', '1']  interval_lower 503507075/274877906944
noncomputable def e201 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1435820451954,0,true,293427023104,293427023168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨763202803598,0,false,-401429047552,-401429047488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1436732058764,0,true,294124884864,294124884928⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨762291196788,0,false,-402743143040,-402743142976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1435484143129,0,true,293169456896,293169456960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨763539112423,0,false,-400944649408,-400944649344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099692726722,0,true,181084032,181084096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099330528830,0,false,-181113920,-181113856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511597947,0,false,-29888,-29824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1435652295403,0,true,293298245888,293298245952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨763370960149,0,false,-401186818688,-401186818624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1436732067451,0,true,294124891520,294124891584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨762291188101,0,false,-402743155584,-402743155520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨996086050399,0,false,-108618264000,-108618263936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨996747322627,0,false,-107888572800,-107888572736⟩
    { al := (78303/256000), au := (314061/1024000), zl := (999/1000), zu := 1,
      A := ⟨336308824178,337220430988⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293427023104,293427023168⟩ : DyadicInterval 40),(⟨-401429047552,-401429047488⟩ : DyadicInterval 40),(⟨709856202610,709856221940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294124884864,294124884928⟩ : DyadicInterval 40),(⟨-402743143040,-402743142976⟩ : DyadicInterval 40),(⟨709567732507,709567751836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293169456896,293169456960⟩ : DyadicInterval 40),(⟨-400944649408,-400944649344⟩ : DyadicInterval 40),(⟨709962414087,709962433416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294124884864,294124884928⟩ : DyadicInterval 40),(⟨-402743143040,-402743142976⟩ : DyadicInterval 40),(⟨709567732507,709567751836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,181098946⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181084032,181084096⟩ : DyadicInterval 40),(⟨-181113920,-181113856⟩ : DyadicInterval 40),(⟨762123368667,762123387996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29888,0⟩ : DyadicInterval 40),(⟨762123383616,762123417824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨336140667627,337220439675⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293298245888,293298245952⟩ : DyadicInterval 40),(⟨-401186818688,-401186818624⟩ : DyadicInterval 40),(⟨709909323206,709909342536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294124891520,294124891584⟩ : DyadicInterval 40),(⟨-402743155584,-402743155520⟩ : DyadicInterval 40),(⟨709567729753,709567749083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-108618264000,-107888572736⟩ : DyadicInterval 40),(⟨816067669984,816432534880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨293427023104,294124884928⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-402743143040,-401429047488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e201_ok : ecellOkT e201 = true := by decide +kernel
theorem e201_pos {a z : ℝ} (ha1 : ((78303/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314061/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e201 e201_ok ha1 ha2 hz1 hz2 hz

-- box ['314061/1024000', '31491/102400', '999/1000', '1']  interval_lower 2086451831/1099511627776
noncomputable def e202 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1436732058763,0,true,294124884864,294124884928⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨762291196789,0,false,-402743143040,-402743142976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1437643665572,0,true,294822304000,294822304064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨761379589980,0,false,-404058811008,-404058810944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1436394838331,0,true,293866784320,293866784384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨762628417221,0,false,-402256851456,-402256851392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099693290352,0,true,181647552,181647616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099329965200,0,false,-181677632,-181677568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511597761,0,false,-30016,-29952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1436563446437,0,true,293995840576,293995840640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨762459809115,0,false,-402499967296,-402499967232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1437643674257,0,true,294822310656,294822310720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨761379581295,0,false,-404058823552,-404058823488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨995526114599,0,false,-109236512832,-109236512768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨996189456739,0,false,-108504126720,-108504126656⟩
    { al := (314061/1024000), au := (31491/102400), zl := (999/1000), zu := 1,
      A := ⟨337220430987,338132037796⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294124884864,294124884928⟩ : DyadicInterval 40),(⟨-402743143040,-402743142976⟩ : DyadicInterval 40),(⟨709567732507,709567751836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294822304000,294822304064⟩ : DyadicInterval 40),(⟨-404058811008,-404058810944⟩ : DyadicInterval 40),(⟨709278428107,709278447436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293866784320,293866784384⟩ : DyadicInterval 40),(⟨-402256851456,-402256851392⟩ : DyadicInterval 40),(⟨709674540220,709674559550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294822304000,294822304064⟩ : DyadicInterval 40),(⟨-404058811008,-404058810944⟩ : DyadicInterval 40),(⟨709278428107,709278447436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,181662576⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181647552,181647616⟩ : DyadicInterval 40),(⟨-181677632,-181677568⟩ : DyadicInterval 40),(⟨762123368577,762123387906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30016,0⟩ : DyadicInterval 40),(⟨762123383616,762123417888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨337051818661,338132046481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨293995840576,293995840640⟩ : DyadicInterval 40),(⟨-402499967296,-402499967232⟩ : DyadicInterval 40),(⟨709621151275,709621170605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294822310656,294822310720⟩ : DyadicInterval 40),(⟨-404058823552,-404058823488⟩ : DyadicInterval 40),(⟨709278425338,709278444668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-109236512832,-108504126656⟩ : DyadicInterval 40),(⟨816375446944,816741659296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨294124884864,294822304064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-404058811008,-402743142976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e202_ok : ecellOkT e202 = true := by decide +kernel
theorem e202_pos {a z : ℝ} (ha1 : ((314061/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31491/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e202 e202_ok ha1 ha2 hz1 hz2 hz

-- box ['31491/102400', '315759/1024000', '999/1000', '1']  interval_lower 269969239/137438953472
noncomputable def e203 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1437643665571,0,true,294822304000,294822304064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨761379589981,0,false,-404058811008,-404058810944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1438555272381,0,true,295519281088,295519281152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨760467983171,0,false,-405376055168,-405376055104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1437305533533,0,true,294563669824,294563669888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨761717722019,0,false,-403570621440,-403570621376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099693854658,0,true,182211776,182211840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099329400894,0,false,-182242048,-182241984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511597574,0,false,-30208,-30144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1437474597476,0,true,294692992896,294692992960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨761548658076,0,false,-403814686080,-403814686016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1438555281077,0,true,295519287680,295519287744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨760467974475,0,false,-405376067712,-405376067648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨994964667162,0,false,-109856779968,-109856779904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨995630080730,0,false,-109121693184,-109121693120⟩
    { al := (31491/102400), au := (315759/1024000), zl := (999/1000), zu := 1,
      A := ⟨338132037795,339043644605⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294822304000,294822304064⟩ : DyadicInterval 40),(⟨-404058811008,-404058810944⟩ : DyadicInterval 40),(⟨709278428107,709278447436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295519281088,295519281152⟩ : DyadicInterval 40),(⟨-405376055168,-405376055104⟩ : DyadicInterval 40),(⟨708988288911,708988308241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294563669824,294563669888⟩ : DyadicInterval 40),(⟨-403570621440,-403570621376⟩ : DyadicInterval 40),(⟨709385833875,709385853204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295519281088,295519281152⟩ : DyadicInterval 40),(⟨-405376055168,-405376055104⟩ : DyadicInterval 40),(⟨708988288911,708988308241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,182226882⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182211776,182211840⟩ : DyadicInterval 40),(⟨-182242048,-182241984⟩ : DyadicInterval 40),(⟨762123368486,762123387816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30208,0⟩ : DyadicInterval 40),(⟨762123383616,762123417984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨337962969700,339043653301⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨294692992896,294692992960⟩ : DyadicInterval 40),(⟨-403814686080,-403814686016⟩ : DyadicInterval 40),(⟨709332146008,709332165338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295519287680,295519287744⟩ : DyadicInterval 40),(⟨-405376067712,-405376067648⟩ : DyadicInterval 40),(⟨708988286165,708988305495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-109856779968,-109121693120⟩ : DyadicInterval 40),(⟨816684230176,817051792864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨294822304000,295519281152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-405376055168,-404058810944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e203_ok : ecellOkT e203 = true := by decide +kernel
theorem e203_pos {a z : ℝ} (ha1 : ((31491/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((315759/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e203 e203_ok ha1 ha2 hz1 hz2 hz

-- box ['315759/1024000', '4947/16000', '999/1000', '1']  interval_lower 2233942455/1099511627776
noncomputable def e204 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1438555272380,0,true,295519281088,295519281152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨760467983172,0,false,-405376055168,-405376055104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1439466879189,0,true,296215816576,296215816640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨759556376363,0,false,-406694879296,-406694879232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1438216228735,0,true,295260113856,295260113920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨760807026817,0,false,-404885963008,-404885962944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099694419640,0,true,182776640,182776704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099328835912,0,false,-182807104,-182807040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511597387,0,false,-30400,-30336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1438385748521,0,true,295389703552,295389703616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨760637507031,0,false,-405130978816,-405130978752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1439466887880,0,true,296215823232,296215823296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨759556367672,0,false,-406694891840,-406694891776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨994401708105,0,false,-110479068608,-110479068544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨995069194600,0,false,-109741275264,-109741275200⟩
    { al := (315759/1024000), au := (4947/16000), zl := (999/1000), zu := 1,
      A := ⟨339043644604,339955251413⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295519281088,295519281152⟩ : DyadicInterval 40),(⟨-405376055168,-405376055104⟩ : DyadicInterval 40),(⟨708988288911,708988308241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296215816576,296215816640⟩ : DyadicInterval 40),(⟨-406694879296,-406694879232⟩ : DyadicInterval 40),(⟨708697314521,708697333851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295260113856,295260113920⟩ : DyadicInterval 40),(⟨-404885963008,-404885962944⟩ : DyadicInterval 40),(⟨709096294622,709096313951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296215816576,296215816640⟩ : DyadicInterval 40),(⟨-406694879296,-406694879232⟩ : DyadicInterval 40),(⟨708697314521,708697333851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,182791864⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182776640,182776704⟩ : DyadicInterval 40),(⟨-182807104,-182807040⟩ : DyadicInterval 40),(⟨762123368394,762123387724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30400,0⟩ : DyadicInterval 40),(⟨762123383616,762123418080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨338874120745,339955260104⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295389703552,295389703616⟩ : DyadicInterval 40),(⟨-405130978816,-405130978752⟩ : DyadicInterval 40),(⟨709042306848,709042326177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296215823232,296215823296⟩ : DyadicInterval 40),(⟨-406694891840,-406694891776⟩ : DyadicInterval 40),(⟨708697311719,708697331049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-110479068608,-109741275200⟩ : DyadicInterval 40),(⟨816994021216,817362937184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨295519281088,296215816640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-406694879296,-405376055104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e204_ok : ecellOkT e204 = true := by decide +kernel
theorem e204_pos {a z : ℝ} (ha1 : ((315759/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4947/16000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e204 e204_ok ha1 ha2 hz1 hz2 hz

-- box ['4947/16000', '317457/1024000', '999/1000', '1']  interval_lower 2309024223/1099511627776
noncomputable def e205 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1439466879188,0,true,296215816576,296215816640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨759556376364,0,false,-406694879296,-406694879232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1440378485998,0,true,296911911104,296911911168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨758644769554,0,false,-408015287168,-408015287104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1439126923936,0,true,295956117056,295956117120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨759896331616,0,false,-406202880064,-406202880000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099694985304,0,true,183342208,183342272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099328270248,0,false,-183372864,-183372800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511597198,0,false,-30592,-30528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1439296899556,0,true,296085972928,296085972992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨759726355996,0,false,-406448849280,-406448849216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1440378494693,0,true,296911917760,296911917824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨758644760859,0,false,-408015299776,-408015299712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨993837237413,0,false,-111103382016,-111103381952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨994506798358,0,false,-110362876288,-110362876224⟩
    { al := (4947/16000), au := (317457/1024000), zl := (999/1000), zu := 1,
      A := ⟨339955251412,340866858222⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296215816576,296215816640⟩ : DyadicInterval 40),(⟨-406694879296,-406694879232⟩ : DyadicInterval 40),(⟨708697314521,708697333851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296911911104,296911911168⟩ : DyadicInterval 40),(⟨-408015287168,-408015287104⟩ : DyadicInterval 40),(⟨708405504405,708405523734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨295956117056,295956117120⟩ : DyadicInterval 40),(⟨-406202880064,-406202880000⟩ : DyadicInterval 40),(⟨708805921987,708805941317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296911911104,296911911168⟩ : DyadicInterval 40),(⟨-408015287168,-408015287104⟩ : DyadicInterval 40),(⟨708405504405,708405523734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,183357528⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183342208,183342272⟩ : DyadicInterval 40),(⟨-183372864,-183372800⟩ : DyadicInterval 40),(⟨762123368302,762123387632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30592,0⟩ : DyadicInterval 40),(⟨762123383616,762123418176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨339785271780,340866866917⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296085972928,296085972992⟩ : DyadicInterval 40),(⟨-406448849280,-406448849216⟩ : DyadicInterval 40),(⟨708751633444,708751652774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296911917760,296911917824⟩ : DyadicInterval 40),(⟨-408015299776,-408015299712⟩ : DyadicInterval 40),(⟨708405501607,708405520937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-111103382016,-110362876224⟩ : DyadicInterval 40),(⟨817304821728,817675093888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨296215816576,296911911168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-408015287168,-406694879232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e205_ok : ecellOkT e205 = true := by decide +kernel
theorem e205_pos {a z : ℝ} (ha1 : ((4947/16000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((317457/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e205 e205_ok ha1 ha2 hz1 hz2 hz

-- box ['317457/1024000', '159153/512000', '999/1000', '1']  interval_lower 2385007171/1099511627776
noncomputable def e206 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1440378485997,0,true,296911911104,296911911168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨758644769555,0,false,-408015287168,-408015287104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1441290092807,0,true,297607565248,297607565312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨757733162745,0,false,-409337282688,-409337282624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1440037619138,0,true,296651679936,296651680000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨758985636414,0,false,-407521376320,-407521376256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099695551650,0,true,183908480,183908544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099327703902,0,false,-183939264,-183939200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511597009,0,false,-30784,-30720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1440208050593,0,true,296781801728,296781801792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨758815204959,0,false,-407768301184,-407768301120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1441290101506,0,true,297607571904,297607571968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨757733154046,0,false,-409337295296,-409337295232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨993271255092,0,false,-111729723392,-111729723328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨993942891996,0,false,-110986499456,-110986499392⟩
    { al := (317457/1024000), au := (159153/512000), zl := (999/1000), zu := 1,
      A := ⟨340866858221,341778465031⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296911911104,296911911168⟩ : DyadicInterval 40),(⟨-408015287168,-408015287104⟩ : DyadicInterval 40),(⟨708405504405,708405523734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨297607565248,297607565312⟩ : DyadicInterval 40),(⟨-409337282688,-409337282624⟩ : DyadicInterval 40),(⟨708112858108,708112877437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296651679936,296651680000⟩ : DyadicInterval 40),(⟨-407521376320,-407521376256⟩ : DyadicInterval 40),(⟨708514715506,708514734836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨297607565248,297607565312⟩ : DyadicInterval 40),(⟨-409337282688,-409337282624⟩ : DyadicInterval 40),(⟨708112858108,708112877437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,183923874⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183908480,183908544⟩ : DyadicInterval 40),(⟨-183939264,-183939200⟩ : DyadicInterval 40),(⟨762123368177,762123387507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30784,0⟩ : DyadicInterval 40),(⟨762123383616,762123418272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨340696422817,341778473730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨296781801728,296781801792⟩ : DyadicInterval 40),(⟨-407768301184,-407768301120⟩ : DyadicInterval 40),(⟨708460125201,708460144531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨297607571904,297607571968⟩ : DyadicInterval 40),(⟨-409337295296,-409337295232⟩ : DyadicInterval 40),(⟨708112855293,708112874622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-111729723392,-110986499392⟩ : DyadicInterval 40),(⟨817616633312,817988264576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨296911911104,297607565312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-409337282688,-408015287104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e206_ok : ecellOkT e206 = true := by decide +kernel
theorem e206_pos {a z : ℝ} (ha1 : ((317457/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159153/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e206 e206_ok ha1 ha2 hz1 hz2 hz

-- box ['159153/512000', '63831/204800', '999/1000', '1']  interval_lower 2461898593/1099511627776
noncomputable def e207 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1441290092806,0,true,297607565248,297607565312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨757733162746,0,false,-409337282688,-409337282624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1442201699615,0,true,298302779520,298302779584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨756821555937,0,false,-410660869632,-410660869568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1440948314340,0,true,297346803072,297346803136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨758074941212,0,false,-408841455552,-408841455488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099696118682,0,true,184475392,184475456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099327136870,0,false,-184506432,-184506368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511596819,0,false,-30976,-30912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1441119201633,0,true,297477190400,297477190464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨757904053919,0,false,-409089338368,-409089338304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1442201708312,0,true,298302786112,298302786176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨756821547240,0,false,-410660882240,-410660882176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨992703761145,0,false,-112358096064,-112358096000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨993377475514,0,false,-111612147904,-111612147840⟩
    { al := (159153/512000), au := (63831/204800), zl := (999/1000), zu := 1,
      A := ⟨341778465030,342690071839⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨297607565248,297607565312⟩ : DyadicInterval 40),(⟨-409337282688,-409337282624⟩ : DyadicInterval 40),(⟨708112858108,708112877437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298302779520,298302779584⟩ : DyadicInterval 40),(⟨-410660869632,-410660869568⟩ : DyadicInterval 40),(⟨707819375167,707819394497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨297346803072,297346803136⟩ : DyadicInterval 40),(⟨-408841455552,-408841455488⟩ : DyadicInterval 40),(⟨708222674689,708222694019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298302779520,298302779584⟩ : DyadicInterval 40),(⟨-410660869632,-410660869568⟩ : DyadicInterval 40),(⟨707819375167,707819394497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,184490906⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184475392,184475456⟩ : DyadicInterval 40),(⟨-184506432,-184506368⟩ : DyadicInterval 40),(⟨762123368115,762123387445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30976,0⟩ : DyadicInterval 40),(⟨762123383616,762123418368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨341607573857,342690080536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨297477190400,297477190464⟩ : DyadicInterval 40),(⟨-409089338368,-409089338304⟩ : DyadicInterval 40),(⟨708167781731,708167801061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298302786112,298302786176⟩ : DyadicInterval 40),(⟨-410660882240,-410660882176⟩ : DyadicInterval 40),(⟨707819372379,707819391709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-112358096064,-111612147840⟩ : DyadicInterval 40),(⟨817929457536,818302450912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨297607565248,298302779584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-410660869632,-409337282624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e207_ok : ecellOkT e207 = true := by decide +kernel
theorem e207_pos {a z : ℝ} (ha1 : ((159153/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63831/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e207 e207_ok ha1 ha2 hz1 hz2 hz

-- box ['63831/204800', '80001/256000', '999/1000', '1']  interval_lower 634926537/274877906944
noncomputable def e208 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1442201699614,0,true,298302779520,298302779584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨756821555938,0,false,-410660869632,-410660869568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1443113306424,0,true,298997554496,298997554560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨755909949128,0,false,-411986051776,-411986051712⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1441859009542,0,true,298041486976,298041487040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨757164246010,0,false,-410163121600,-410163121536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099696686405,0,true,185043008,185043072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099326569147,0,false,-185074240,-185074176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511596628,0,false,-31168,-31104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1442030352662,0,true,298172139584,298172139648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨756992902890,0,false,-410411964672,-410411964608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1443113315128,0,true,298997561088,298997561152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨755909940424,0,false,-411986064448,-411986064384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨992134755564,0,false,-112988503296,-112988503232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨992810548921,0,false,-112239825088,-112239825024⟩
    { al := (63831/204800), au := (80001/256000), zl := (999/1000), zu := 1,
      A := ⟨342690071838,343601678648⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298302779520,298302779584⟩ : DyadicInterval 40),(⟨-410660869632,-410660869568⟩ : DyadicInterval 40),(⟨707819375167,707819394497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298997554496,298997554560⟩ : DyadicInterval 40),(⟨-411986051776,-411986051712⟩ : DyadicInterval 40),(⟨707525055071,707525074401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298041486976,298041487040⟩ : DyadicInterval 40),(⟨-410163121600,-410163121536⟩ : DyadicInterval 40),(⟨707929799102,707929818431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298997554496,298997554560⟩ : DyadicInterval 40),(⟨-411986051776,-411986051712⟩ : DyadicInterval 40),(⟨707525055071,707525074401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,185058629⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185043008,185043072⟩ : DyadicInterval 40),(⟨-185074240,-185074176⟩ : DyadicInterval 40),(⟨762123368020,762123387350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31168,0⟩ : DyadicInterval 40),(⟨762123383616,762123418464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨342518724886,343601687352⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298172139584,298172139648⟩ : DyadicInterval 40),(⟨-410411964672,-410411964608⟩ : DyadicInterval 40),(⟨707874602517,707874621846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298997561088,298997561152⟩ : DyadicInterval 40),(⟨-411986064448,-411986064384⟩ : DyadicInterval 40),(⟨707525052287,707525071616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-112988503296,-112239825024⟩ : DyadicInterval 40),(⟨818243296128,818617654528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨298302779520,298997554560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-411986051776,-410660869568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e208_ok : ecellOkT e208 = true := by decide +kernel
theorem e208_pos {a z : ℝ} (ha1 : ((63831/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((80001/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e208 e208_ok ha1 ha2 hz1 hz2 hz

-- box ['80001/256000', '320853/1024000', '999/1000', '1']  interval_lower 1309218663/549755813888
noncomputable def e209 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1443113306423,0,true,298997554496,298997554560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨755909949129,0,false,-411986051776,-411986051712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1444024913232,0,true,299691890688,299691890752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨754998342320,0,false,-413312833024,-413312832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1442769704744,0,true,298735732352,298735732416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨756253550808,0,false,-411486378240,-411486378176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099697254819,0,true,185611328,185611392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099326000733,0,false,-185642752,-185642688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511596437,0,false,-31360,-31296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1442941503711,0,true,298866649792,298866649856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨756081751841,0,false,-411736183936,-411736183872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1444024921932,0,true,299691897344,299691897408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨754998333620,0,false,-413312845696,-413312845632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨991564238360,0,false,-113620948352,-113620948288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨992242112198,0,false,-112869534080,-112869534016⟩
    { al := (80001/256000), au := (320853/1024000), zl := (999/1000), zu := 1,
      A := ⟨343601678647,344513285456⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298997554496,298997554560⟩ : DyadicInterval 40),(⟨-411986051776,-411986051712⟩ : DyadicInterval 40),(⟨707525055071,707525074401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨299691890688,299691890752⟩ : DyadicInterval 40),(⟨-413312833024,-413312832960⟩ : DyadicInterval 40),(⟨707229897387,707229916716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298735732352,298735732416⟩ : DyadicInterval 40),(⟨-411486378240,-411486378176⟩ : DyadicInterval 40),(⟨707636088155,707636107485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨299691890688,299691890752⟩ : DyadicInterval 40),(⟨-413312833024,-413312832960⟩ : DyadicInterval 40),(⟨707229897387,707229916716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,185627043⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185611328,185611392⟩ : DyadicInterval 40),(⟨-185642752,-185642688⟩ : DyadicInterval 40),(⟨762123367924,762123387254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31360,0⟩ : DyadicInterval 40),(⟨762123383616,762123418560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨343429875935,344513294156⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨298866649792,298866649856⟩ : DyadicInterval 40),(⟨-411736183936,-411736183872⟩ : DyadicInterval 40),(⟨707580587103,707580606432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨299691897344,299691897408⟩ : DyadicInterval 40),(⟨-413312845696,-413312845632⟩ : DyadicInterval 40),(⟨707229894546,707229913875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-113620948352,-112869534016⟩ : DyadicInterval 40),(⟨818558150624,818933877056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨298997554496,299691890752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-413312833024,-411986051712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e209_ok : ecellOkT e209 = true := by decide +kernel
theorem e209_pos {a z : ℝ} (ha1 : ((80001/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((320853/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e209 e209_ok ha1 ha2 hz1 hz2 hz

-- box ['320853/1024000', '160851/512000', '999/1000', '1']  interval_lower 168631229/68719476736
noncomputable def e210 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1444024913231,0,true,299691890688,299691890752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨754998342321,0,false,-413312833024,-413312832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1444936520041,0,true,300385788736,300385788800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨754086735511,0,false,-414641217280,-414641217216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1443680399945,0,true,299429539584,299429539648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨755342855607,0,false,-412811229376,-412811229312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099697823930,0,true,186180352,186180416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099325431622,0,false,-186211968,-186211904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511596244,0,false,-31552,-31488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1443852654744,0,true,299560721536,299560721600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨755170600808,0,false,-413061999936,-413061999872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1444936528744,0,true,300385795328,300385795392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨754086726808,0,false,-414641229952,-414641229888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨990992209522,0,false,-114255434624,-114255434560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨991672165366,0,false,-113501278336,-113501278272⟩
    { al := (320853/1024000), au := (160851/512000), zl := (999/1000), zu := 1,
      A := ⟨344513285455,345424892265⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨299691890688,299691890752⟩ : DyadicInterval 40),(⟨-413312833024,-413312832960⟩ : DyadicInterval 40),(⟨707229897387,707229916716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300385788736,300385788800⟩ : DyadicInterval 40),(⟨-414641217280,-414641217216⟩ : DyadicInterval 40),(⟨706933901588,706933920918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨299429539584,299429539648⟩ : DyadicInterval 40),(⟨-412811229376,-412811229312⟩ : DyadicInterval 40),(⟨707341541506,707341560836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300385788736,300385788800⟩ : DyadicInterval 40),(⟨-414641217280,-414641217216⟩ : DyadicInterval 40),(⟨706933901588,706933920918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,186196154⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186180352,186180416⟩ : DyadicInterval 40),(⟨-186211968,-186211904⟩ : DyadicInterval 40),(⟨762123367828,762123387158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31552,0⟩ : DyadicInterval 40),(⟨762123383616,762123418656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨344341026968,345424900968⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨299560721536,299560721600⟩ : DyadicInterval 40),(⟨-413061999936,-413061999872⟩ : DyadicInterval 40),(⟨707285735027,707285754357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300385795328,300385795392⟩ : DyadicInterval 40),(⟨-414641229952,-414641229888⟩ : DyadicInterval 40),(⟨706933898772,706933918102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-114255434624,-113501278272⟩ : DyadicInterval 40),(⟨818874022752,819251120192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨299691890688,300385788800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-414641217280,-413312832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e210_ok : ecellOkT e210 = true := by decide +kernel
theorem e210_pos {a z : ℝ} (ha1 : ((320853/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((160851/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e210 e210_ok ha1 ha2 hz1 hz2 hz

-- box ['160851/512000', '322551/1024000', '999/1000', '1']  interval_lower 2778701561/1099511627776
noncomputable def e211 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1444936520040,0,true,300385788736,300385788800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨754086735512,0,false,-414641217280,-414641217216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1445848126850,0,true,301079249088,301079249152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨753175128702,0,false,-415971208320,-415971208256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1444591095147,0,true,300122909312,300122909376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨754432160405,0,false,-414137678720,-414137678656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099698393738,0,true,186750080,186750144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099324861814,0,false,-186781888,-186781824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511596051,0,false,-31744,-31680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1444763805789,0,true,300254355520,300254355584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨754259449763,0,false,-414389416576,-414389416512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1445848135549,0,true,301079255744,301079255808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨753175120003,0,false,-415971221056,-415971220992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨990418669060,0,false,-114891965312,-114891965248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨991100708409,0,false,-114135061056,-114135060992⟩
    { al := (160851/512000), au := (322551/1024000), zl := (999/1000), zu := 1,
      A := ⟨345424892264,346336499074⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300385788736,300385788800⟩ : DyadicInterval 40),(⟨-414641217280,-414641217216⟩ : DyadicInterval 40),(⟨706933901588,706933920918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301079249088,301079249152⟩ : DyadicInterval 40),(⟨-415971208320,-415971208256⟩ : DyadicInterval 40),(⟨706637067226,706637086555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300122909312,300122909376⟩ : DyadicInterval 40),(⟨-414137678720,-414137678656⟩ : DyadicInterval 40),(⟨707046158572,707046177902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301079249088,301079249152⟩ : DyadicInterval 40),(⟨-415971208320,-415971208256⟩ : DyadicInterval 40),(⟨706637067226,706637086555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,186765962⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186750080,186750144⟩ : DyadicInterval 40),(⟨-186781888,-186781824⟩ : DyadicInterval 40),(⟨762123367731,762123387060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31744,0⟩ : DyadicInterval 40),(⟨762123383616,762123418752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨345252178013,346336507773⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300254355520,300254355584⟩ : DyadicInterval 40),(⟨-414389416576,-414389416512⟩ : DyadicInterval 40),(⟨706990045718,706990065047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301079255744,301079255808⟩ : DyadicInterval 40),(⟨-415971221056,-415971220992⟩ : DyadicInterval 40),(⟨706637064375,706637083705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-114891965312,-114135060992⟩ : DyadicInterval 40),(⟨819190914112,819569385536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨300385788736,301079249152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-415971208320,-414641217216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e211_ok : ecellOkT e211 = true := by decide +kernel
theorem e211_pos {a z : ℝ} (ha1 : ((160851/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((322551/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e211 e211_ok ha1 ha2 hz1 hz2 hz

-- box ['322551/1024000', '1617/5120', '999/1000', '1']  interval_lower 357531229/137438953472
noncomputable def e212 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1445848126849,0,true,301079249088,301079249152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨753175128703,0,false,-415971208320,-415971208256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1446759733658,0,true,301772272384,301772272448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨752263521894,0,false,-417302810176,-417302810112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1445501790349,0,true,300815842048,300815842112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨753521465203,0,false,-415465730304,-415465730240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099698964247,0,true,187320512,187320576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099324291305,0,false,-187352448,-187352384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511595857,0,false,-31936,-31872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1445674956824,0,true,300947552128,300947552192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨753348298728,0,false,-415718437696,-415718437632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1446759742349,0,true,301772279040,301772279104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨752263513203,0,false,-417302822848,-417302822784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨989843616971,0,false,-115530543808,-115530543744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨990527741340,0,false,-114770885568,-114770885504⟩
    { al := (322551/1024000), au := (1617/5120), zl := (999/1000), zu := 1,
      A := ⟨346336499073,347248105882⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301079249088,301079249152⟩ : DyadicInterval 40),(⟨-415971208320,-415971208256⟩ : DyadicInterval 40),(⟨706637067226,706637086556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301772272384,301772272448⟩ : DyadicInterval 40),(⟨-417302810176,-417302810112⟩ : DyadicInterval 40),(⟨706339393805,706339413134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300815842048,300815842112⟩ : DyadicInterval 40),(⟨-415465730304,-415465730240⟩ : DyadicInterval 40),(⟨706749938956,706749958285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301772272384,301772272448⟩ : DyadicInterval 40),(⟨-417302810176,-417302810112⟩ : DyadicInterval 40),(⟨706339393805,706339413134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,187336471⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187320512,187320576⟩ : DyadicInterval 40),(⟨-187352448,-187352384⟩ : DyadicInterval 40),(⟨762123367601,762123386930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31936,0⟩ : DyadicInterval 40),(⟨762123383616,762123418848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨346163329048,347248114573⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨300947552128,300947552192⟩ : DyadicInterval 40),(⟨-415718437696,-415718437632⟩ : DyadicInterval 40),(⟨706693518800,706693538129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301772279040,301772279104⟩ : DyadicInterval 40),(⟨-417302822848,-417302822784⟩ : DyadicInterval 40),(⟨706339390919,706339410248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-115530543808,-114770885504⟩ : DyadicInterval 40),(⟨819508826368,819888674784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨301079249088,301772272448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-417302810176,-415971208256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e212_ok : ecellOkT e212 = true := by decide +kernel
theorem e212_pos {a z : ℝ} (ha1 : ((322551/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1617/5120 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e212 e212_ok ha1 ha2 hz1 hz2 hz

-- box ['1617/5120', '324249/1024000', '999/1000', '1']  interval_lower 2942750871/1099511627776
noncomputable def e213 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1446759733657,0,true,301772272384,301772272448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨752263521895,0,false,-417302810176,-417302810112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1447671340467,0,true,302464859200,302464859264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨751351915085,0,false,-418636026560,-418636026496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1446412485551,0,true,301508338368,301508338432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨752610770001,0,false,-416795387904,-416795387840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099699535462,0,true,187891584,187891648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099323720090,0,false,-187923776,-187923712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511595662,0,false,-32128,-32064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1446586107347,0,true,301640311616,301640311680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨752437148205,0,false,-417049066432,-417049066368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1447671349183,0,true,302464865792,302464865856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨751351906369,0,false,-418636039360,-418636039296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨989267053232,0,false,-116171173504,-116171173440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨989953264476,0,false,-115408754816,-115408754752⟩
    { al := (1617/5120), au := (324249/1024000), zl := (999/1000), zu := 1,
      A := ⟨347248105881,348159712691⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301772272384,301772272448⟩ : DyadicInterval 40),(⟨-417302810176,-417302810112⟩ : DyadicInterval 40),(⟨706339393805,706339413135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302464859200,302464859264⟩ : DyadicInterval 40),(⟨-418636026560,-418636026496⟩ : DyadicInterval 40),(⟨706040880753,706040900083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301508338368,301508338432⟩ : DyadicInterval 40),(⟨-416795387904,-416795387840⟩ : DyadicInterval 40),(⟨706452882122,706452901452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302464859200,302464859264⟩ : DyadicInterval 40),(⟨-418636026560,-418636026496⟩ : DyadicInterval 40),(⟨706040880753,706040900083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,187907686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187891584,187891648⟩ : DyadicInterval 40),(⟨-187923776,-187923712⟩ : DyadicInterval 40),(⟨762123367534,762123386863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32128,0⟩ : DyadicInterval 40),(⟨762123383616,762123418944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨347074479571,348159721407⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨301640311616,301640311680⟩ : DyadicInterval 40),(⟨-417049066432,-417049066368⟩ : DyadicInterval 40),(⟨706396153890,706396173220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302464865792,302464865856⟩ : DyadicInterval 40),(⟨-418636039360,-418636039296⟩ : DyadicInterval 40),(⟨706040877929,706040897258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-116171173504,-115408754752⟩ : DyadicInterval 40),(⟨819827760992,820208989632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨301772272384,302464859264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-418636026560,-417302810112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e213_ok : ecellOkT e213 = true := by decide +kernel
theorem e213_pos {a z : ℝ} (ha1 : ((1617/5120 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((324249/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e213 e213_ok ha1 ha2 hz1 hz2 hz

-- box ['324249/1024000', '162549/512000', '999/1000', '1']  interval_lower 3026218609/1099511627776
noncomputable def e214 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1447671340466,0,true,302464859200,302464859264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨751351915086,0,false,-418636026560,-418636026496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1448582947275,0,true,303157009920,303157009984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨750440308277,0,false,-419970861568,-419970861504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1447323180753,0,true,302200398784,302200398848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨751700074799,0,false,-418126655424,-418126655360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099700107384,0,true,188463424,188463488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099323148168,0,false,-188495808,-188495744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511595466,0,false,-32320,-32256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1447497258907,0,true,302332635648,302332635712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨751525996645,0,false,-418381309056,-418381308992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1448582955977,0,true,303157016576,303157016640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨750440299575,0,false,-419970874304,-419970874240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨988688977888,0,false,-116813857728,-116813857664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨989377276839,0,false,-116048673344,-116048673280⟩
    { al := (324249/1024000), au := (162549/512000), zl := (999/1000), zu := 1,
      A := ⟨348159712690,349071319499⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302464859200,302464859264⟩ : DyadicInterval 40),(⟨-418636026560,-418636026496⟩ : DyadicInterval 40),(⟨706040880753,706040900083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303157009920,303157009984⟩ : DyadicInterval 40),(⟨-419970861568,-419970861504⟩ : DyadicInterval 40),(⟨705741527751,705741547081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302200398784,302200398848⟩ : DyadicInterval 40),(⟨-418126655424,-418126655360⟩ : DyadicInterval 40),(⟨706154987617,706155006946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303157009920,303157009984⟩ : DyadicInterval 40),(⟨-419970861568,-419970861504⟩ : DyadicInterval 40),(⟨705741527751,705741547081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,188479608⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188463424,188463488⟩ : DyadicInterval 40),(⟨-188495808,-188495744⟩ : DyadicInterval 40),(⟨762123367434,762123386763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32320,0⟩ : DyadicInterval 40),(⟨762123383616,762123419040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨347985631131,349071328201⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302332635648,302332635712⟩ : DyadicInterval 40),(⟨-418381309056,-418381308992⟩ : DyadicInterval 40),(⟨706097950077,706097969406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303157016576,303157016640⟩ : DyadicInterval 40),(⟨-419970874304,-419970874240⟩ : DyadicInterval 40),(⟨705741524852,705741544181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-116813857728,-116048673280⟩ : DyadicInterval 40),(⟨820147720256,820530331744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨302464859200,303157009984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-419970861568,-418636026496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e214_ok : ecellOkT e214 = true := by decide +kernel
theorem e214_pos {a z : ℝ} (ha1 : ((324249/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162549/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e214 e214_ok ha1 ha2 hz1 hz2 hz

-- box ['162549/512000', '325947/1024000', '999/1000', '1']  interval_lower 1555327401/549755813888
noncomputable def e215 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1448582947274,0,true,303157009920,303157009984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨750440308278,0,false,-419970861568,-419970861504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1449494554084,0,true,303848725248,303848725312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨749528701468,0,false,-421307319104,-421307319040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1448233875954,0,true,302892023936,302892024000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨750789379598,0,false,-419459536768,-419459536704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099700680017,0,true,189035968,189036032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099322575535,0,false,-189068544,-189068480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511595269,0,false,-32512,-32448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1448408409945,0,true,303024523648,303024523712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨750614845607,0,false,-419715167040,-419715166976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1449494562779,0,true,303848731840,303848731904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨749528692773,0,false,-421307331840,-421307331776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨988109390911,0,false,-117458599936,-117458599872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨988799779413,0,false,-116690643328,-116690643264⟩
    { al := (162549/512000), au := (325947/1024000), zl := (999/1000), zu := 1,
      A := ⟨349071319498,349982926308⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303157009920,303157009984⟩ : DyadicInterval 40),(⟨-419970861568,-419970861504⟩ : DyadicInterval 40),(⟨705741527752,705741547081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303848725248,303848725312⟩ : DyadicInterval 40),(⟨-421307319104,-421307319040⟩ : DyadicInterval 40),(⟨705441334196,705441353525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨302892023936,302892024000⟩ : DyadicInterval 40),(⟨-419459536768,-419459536704⟩ : DyadicInterval 40),(⟨705856254893,705856274222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303848725248,303848725312⟩ : DyadicInterval 40),(⟨-421307319104,-421307319040⟩ : DyadicInterval 40),(⟨705441334196,705441353525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,189052241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189035968,189036032⟩ : DyadicInterval 40),(⟨-189068544,-189068480⟩ : DyadicInterval 40),(⟨762123367333,762123386663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32512,0⟩ : DyadicInterval 40),(⟨762123383616,762123419136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨348896782169,349982935003⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303024523648,303024523712⟩ : DyadicInterval 40),(⟨-419715167040,-419715166976⟩ : DyadicInterval 40),(⟨705798907286,705798926615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303848731840,303848731904⟩ : DyadicInterval 40),(⟨-421307331840,-421307331776⟩ : DyadicInterval 40),(⟨705441331324,705441350654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-117458599936,-116690643264⟩ : DyadicInterval 40),(⟨820468705248,820852702848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨303157009920,303848725312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-421307319104,-419970861504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e215_ok : ecellOkT e215 = true := by decide +kernel
theorem e215_pos {a z : ℝ} (ha1 : ((162549/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325947/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e215 e215_ok ha1 ha2 hz1 hz2 hz

-- box ['325947/1024000', '81699/256000', '999/1000', '1']  interval_lower 799017317/274877906944
noncomputable def e216 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1449494554083,0,true,303848725248,303848725312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨749528701469,0,false,-421307319104,-421307319040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1450406160892,0,true,304540005696,304540005760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨748617094660,0,false,-422645403008,-422645402944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1449144571156,0,true,303583214272,303583214336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨749878684396,0,false,-420794035904,-420794035840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099701253363,0,true,189609216,189609280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099322002189,0,false,-189641984,-189641920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511595072,0,false,-32768,-32704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1449319560979,0,true,303715976512,303715976576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨749703694573,0,false,-421050645120,-421050645056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1450406169595,0,true,304540012288,304540012352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨748617085957,0,false,-422645415808,-422645415744⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨987528292295,0,false,-118105403456,-118105403392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨988220771872,0,false,-117334668544,-117334668480⟩
    { al := (325947/1024000), au := (81699/256000), zl := (999/1000), zu := 1,
      A := ⟨349982926307,350894533116⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303848725248,303848725312⟩ : DyadicInterval 40),(⟨-421307319104,-421307319040⟩ : DyadicInterval 40),(⟨705441334196,705441353525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304540005696,304540005760⟩ : DyadicInterval 40),(⟨-422645403008,-422645402944⟩ : DyadicInterval 40),(⟨705140299579,705140318909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303583214272,303583214336⟩ : DyadicInterval 40),(⟨-420794035904,-420794035840⟩ : DyadicInterval 40),(⟨705556683542,705556702871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304540005696,304540005760⟩ : DyadicInterval 40),(⟨-422645403008,-422645402944⟩ : DyadicInterval 40),(⟨705140299579,705140318909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,189625587⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189609216,189609280⟩ : DyadicInterval 40),(⟨-189641984,-189641920⟩ : DyadicInterval 40),(⟨762123367232,762123386561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32768,0⟩ : DyadicInterval 40),(⟨762123383616,762123419264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨349807933203,350894541819⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨303715976512,303715976576⟩ : DyadicInterval 40),(⟨-421050645120,-421050645056⟩ : DyadicInterval 40),(⟨705499024906,705499044235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304540012288,304540012352⟩ : DyadicInterval 40),(⟨-422645415808,-422645415744⟩ : DyadicInterval 40),(⟨705140296711,705140316040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-118105403456,-117334668480⟩ : DyadicInterval 40),(⟨820790717856,821176104608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨303848725248,304540005760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-422645403008,-421307319040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e216_ok : ecellOkT e216 = true := by decide +kernel
theorem e216_pos {a z : ℝ} (ha1 : ((325947/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((81699/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e216 e216_ok ha1 ha2 hz1 hz2 hz

-- box ['81699/256000', '65529/204800', '999/1000', '1']  interval_lower 3282468747/1099511627776
noncomputable def e217 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1450406160891,0,true,304540005696,304540005760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨748617094661,0,false,-422645403008,-422645402944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1451317767701,0,true,305230851776,305230851840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨747705487851,0,false,-423985117376,-423985117312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1450055266357,0,true,304273970368,304273970432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨748967989195,0,false,-422130156672,-422130156608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099701827426,0,true,190183168,190183232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099321428126,0,false,-190216128,-190216064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511594874,0,false,-32960,-32896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1450230711510,0,true,304406994496,304406994560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨748792544042,0,false,-422387746560,-422387746496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1451317776397,0,true,305230858368,305230858432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨747705479155,0,false,-423985130112,-423985130048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨986945682058,0,false,-118754271744,-118754271680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨987640254534,0,false,-117980752000,-117980751936⟩
    { al := (81699/256000), au := (65529/204800), zl := (999/1000), zu := 1,
      A := ⟨350894533115,351806139925⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304540005696,304540005760⟩ : DyadicInterval 40),(⟨-422645403008,-422645402944⟩ : DyadicInterval 40),(⟨705140299579,705140318909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305230851776,305230851840⟩ : DyadicInterval 40),(⟨-423985117376,-423985117312⟩ : DyadicInterval 40),(⟨704838423474,704838442803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304273970368,304273970432⟩ : DyadicInterval 40),(⟨-422130156672,-422130156608⟩ : DyadicInterval 40),(⟨705256273024,705256292353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305230851776,305230851840⟩ : DyadicInterval 40),(⟨-423985117376,-423985117312⟩ : DyadicInterval 40),(⟨704838423474,704838442803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,190199650⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190183168,190183232⟩ : DyadicInterval 40),(⟨-190216128,-190216064⟩ : DyadicInterval 40),(⟨762123367130,762123386459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32960,0⟩ : DyadicInterval 40),(⟨762123383616,762123419360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨350719083734,351806148621⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304406994496,304406994560⟩ : DyadicInterval 40),(⟨-422387746560,-422387746496⟩ : DyadicInterval 40),(⟨705198302572,705198321902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305230858368,305230858432⟩ : DyadicInterval 40),(⟨-423985130112,-423985130048⟩ : DyadicInterval 40),(⟨704838420570,704838439899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-118754271744,-117980751936⟩ : DyadicInterval 40),(⟨821113759584,821500538752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨304540005696,305230851840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-423985117376,-422645402944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e217_ok : ecellOkT e217 = true := by decide +kernel
theorem e217_pos {a z : ℝ} (ha1 : ((81699/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((65529/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e217 e217_ok ha1 ha2 hz1 hz2 hz

-- box ['65529/204800', '164247/512000', '999/1000', '1']  interval_lower 3369865155/1099511627776
noncomputable def e218 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1451317767700,0,true,305230851776,305230851840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨747705487852,0,false,-423985117376,-423985117312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1452229374510,0,true,305921264064,305921264128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨746793881042,0,false,-425326466048,-425326465984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1450965961560,0,true,304964292800,304964292864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨748057293992,0,false,-423467903040,-423467902976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099702402209,0,true,190757824,190757888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099320853343,0,false,-190791040,-190790976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511594675,0,false,-33152,-33088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1451141862552,0,true,305097578816,305097578880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨747881393000,0,false,-423726476736,-423726476672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1452229383214,0,true,305921270656,305921270720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨746793872338,0,false,-425326478912,-425326478848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨986361560183,0,false,-119405208192,-119405208128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨987058226753,0,false,-118628897920,-118628897856⟩
    { al := (65529/204800), au := (164247/512000), zl := (999/1000), zu := 1,
      A := ⟨351806139924,352717746734⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305230851776,305230851840⟩ : DyadicInterval 40),(⟨-423985117376,-423985117312⟩ : DyadicInterval 40),(⟨704838423474,704838442803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305921264064,305921264128⟩ : DyadicInterval 40),(⟨-425326466048,-425326465984⟩ : DyadicInterval 40),(⟨704535705316,704535724646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨304964292800,304964292864⟩ : DyadicInterval 40),(⟨-423467903040,-423467902976⟩ : DyadicInterval 40),(⟨704955022832,704955042161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305921264064,305921264128⟩ : DyadicInterval 40),(⟨-425326466048,-425326465984⟩ : DyadicInterval 40),(⟨704535705316,704535724646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,190774433⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190757824,190757888⟩ : DyadicInterval 40),(⟨-190791040,-190790976⟩ : DyadicInterval 40),(⟨762123367058,762123386388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33152,0⟩ : DyadicInterval 40),(⟨762123383616,762123419456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨351630234776,352717755438⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305097578816,305097578880⟩ : DyadicInterval 40),(⟨-423726476736,-423726476672⟩ : DyadicInterval 40),(⟨704896739498,704896758827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305921270656,305921270720⟩ : DyadicInterval 40),(⟨-425326478912,-425326478848⟩ : DyadicInterval 40),(⟨704535702438,704535721767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-119405208192,-118628897856⟩ : DyadicInterval 40),(⟨821437832544,821826006976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨305230851776,305921264128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-425326466048,-423985117312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e218_ok : ecellOkT e218 = true := by decide +kernel
theorem e218_pos {a z : ℝ} (ha1 : ((65529/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164247/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e218 e218_ok ha1 ha2 hz1 hz2 hz

-- box ['164247/512000', '329343/1024000', '999/1000', '1']  interval_lower 3458264059/1099511627776
noncomputable def e219 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1452229374509,0,true,305921264064,305921264128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨746793881043,0,false,-425326466048,-425326465984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1453140981318,0,true,306611243136,306611243200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨745882274234,0,false,-426669453184,-426669453120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1451876656762,0,true,305654182080,305654182144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨747146598790,0,false,-424807279040,-424807278976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099702977715,0,true,191333248,191333312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099320277837,0,false,-191366592,-191366528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511594475,0,false,-33344,-33280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1452053013596,0,true,305787729664,305787729728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨746970241956,0,false,-425066838912,-425066838848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1453140990028,0,true,306611249728,306611249792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨745882265524,0,false,-426669465984,-426669465920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨985775926681,0,false,-120058216256,-120058216192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨986474688852,0,false,-119279109248,-119279109184⟩
    { al := (164247/512000), au := (329343/1024000), zl := (999/1000), zu := 1,
      A := ⟨352717746733,353629353542⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305921264064,305921264128⟩ : DyadicInterval 40),(⟨-425326466048,-425326465984⟩ : DyadicInterval 40),(⟨704535705317,704535724646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨306611243136,306611243200⟩ : DyadicInterval 40),(⟨-426669453184,-426669453120⟩ : DyadicInterval 40),(⟨704232144645,704232163975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305654182080,305654182144⟩ : DyadicInterval 40),(⟨-424807279040,-424807278976⟩ : DyadicInterval 40),(⟨704652932518,704652951848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨306611243136,306611243200⟩ : DyadicInterval 40),(⟨-426669453184,-426669453120⟩ : DyadicInterval 40),(⟨704232144645,704232163975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,191349939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191333248,191333312⟩ : DyadicInterval 40),(⟨-191366592,-191366528⟩ : DyadicInterval 40),(⟨762123366922,762123386252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33344,0⟩ : DyadicInterval 40),(⟨762123383616,762123419552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨352541385820,353629362252⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨305787729664,305787729728⟩ : DyadicInterval 40),(⟨-425066838912,-425066838848⟩ : DyadicInterval 40),(⟨704594335348,704594354677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨306611249728,306611249792⟩ : DyadicInterval 40),(⟨-426669465984,-426669465920⟩ : DyadicInterval 40),(⟨704232141726,704232161056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-120058216256,-119279109184⟩ : DyadicInterval 40),(⟨821762938208,822152511008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨305921264064,306611243200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-426669453184,-425326465984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e219_ok : ecellOkT e219 = true := by decide +kernel
theorem e219_pos {a z : ℝ} (ha1 : ((164247/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((329343/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e219 e219_ok ha1 ha2 hz1 hz2 hz

-- box ['329343/1024000', '20637/64000', '999/1000', '1']  interval_lower 3547674363/1099511627776
noncomputable def e220 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1453140981317,0,true,306611243136,306611243200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨745882274235,0,false,-426669453184,-426669453120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1454052588127,0,true,307300789440,307300789504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨744970667425,0,false,-428014082688,-428014082624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1452787351963,0,true,306343638720,306343638784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨746235903589,0,false,-426148288576,-426148288512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099703553948,0,true,191909376,191909440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099319701604,0,false,-191942976,-191942912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511594274,0,false,-33536,-33472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1452964164634,0,true,306477447552,306477447616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨746059090918,0,false,-426408837056,-426408836992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1454052596829,0,true,307300796032,307300796096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨744970658723,0,false,-428014095488,-428014095424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨985188781558,0,false,-120713299456,-120713299392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨985889640837,0,false,-119931389440,-119931389376⟩
    { al := (329343/1024000), au := (20637/64000), zl := (999/1000), zu := 1,
      A := ⟨353629353541,354540960351⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨306611243136,306611243200⟩ : DyadicInterval 40),(⟨-426669453184,-426669453120⟩ : DyadicInterval 40),(⟨704232144646,704232163975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307300789440,307300789504⟩ : DyadicInterval 40),(⟨-428014082688,-428014082624⟩ : DyadicInterval 40),(⟨703927740987,703927760316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨306343638720,306343638784⟩ : DyadicInterval 40),(⟨-426148288576,-426148288512⟩ : DyadicInterval 40),(⟨704350001584,704350020913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307300789440,307300789504⟩ : DyadicInterval 40),(⟨-428014082688,-428014082624⟩ : DyadicInterval 40),(⟨703927740987,703927760316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,191926172⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191909376,191909440⟩ : DyadicInterval 40),(⟨-191942976,-191942912⟩ : DyadicInterval 40),(⟨762123366850,762123386179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33536,0⟩ : DyadicInterval 40),(⟨762123383616,762123419648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨353452536858,354540969053⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨306477447552,306477447616⟩ : DyadicInterval 40),(⟨-426408837056,-426408836992⟩ : DyadicInterval 40),(⟨704291089642,704291108971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307300796032,307300796096⟩ : DyadicInterval 40),(⟨-428014095488,-428014095424⟩ : DyadicInterval 40),(⟨703927738054,703927757384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-120713299456,-119931389376⟩ : DyadicInterval 40),(⟨822089078304,822480052608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨306611243136,307300789504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-428014082688,-426669453120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e220_ok : ecellOkT e220 = true := by decide +kernel
theorem e220_pos {a z : ℝ} (ha1 : ((329343/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20637/64000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e220 e220_ok ha1 ha2 hz1 hz2 hz

-- box ['20637/64000', '331041/1024000', '999/1000', '1']  interval_lower 1819052061/549755813888
noncomputable def e221 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1454052588126,0,true,307300789440,307300789504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨744970667426,0,false,-428014082688,-428014082560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1454964194935,0,true,307989903616,307989903680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨744059060617,0,false,-429360358528,-429360358464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1453698047165,0,true,307032663360,307032663424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨745325208387,0,false,-427490935616,-427490935552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099704130909,0,true,192486272,192486336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099319124643,0,false,-192520000,-192519936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511594072,0,false,-33728,-33664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1453875315678,0,true,307166733120,307166733184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨745147939874,0,false,-427752475136,-427752475072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1454964203652,0,true,307989910208,307989910272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨744059051900,0,false,-429360371456,-429360371392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨984600124791,0,false,-121370461184,-121370461120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨985303082700,0,false,-120585742016,-120585741952⟩
    { al := (20637/64000), au := (331041/1024000), zl := (999/1000), zu := 1,
      A := ⟨354540960350,355452567159⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307300789440,307300789504⟩ : DyadicInterval 40),(⟨-428014082688,-428014082560⟩ : DyadicInterval 40),(⟨703927740965,703927760317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307989903616,307989903680⟩ : DyadicInterval 40),(⟨-429360358528,-429360358464⟩ : DyadicInterval 40),(⟨703622493756,703622513086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307032663360,307032663424⟩ : DyadicInterval 40),(⟨-427490935616,-427490935552⟩ : DyadicInterval 40),(⟨704046229456,704046248786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307989903616,307989903680⟩ : DyadicInterval 40),(⟨-429360358528,-429360358464⟩ : DyadicInterval 40),(⟨703622493756,703622513086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,192503133⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192486272,192486336⟩ : DyadicInterval 40),(⟨-192520000,-192519936⟩ : DyadicInterval 40),(⟨762123366712,762123386041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33728,0⟩ : DyadicInterval 40),(⟨762123383616,762123419744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨354363687902,355452575876⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307166733120,307166733184⟩ : DyadicInterval 40),(⟨-427752475136,-427752475072⟩ : DyadicInterval 40),(⟨703987001804,703987021133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307989910208,307989910272⟩ : DyadicInterval 40),(⟨-429360371456,-429360371392⟩ : DyadicInterval 40),(⟨703622490846,703622510175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-121370461184,-120585741952⟩ : DyadicInterval 40),(⟨822416254592,822808633472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨307300789440,307989903680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-429360358528,-428014082560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e221_ok : ecellOkT e221 = true := by decide +kernel
theorem e221_pos {a z : ℝ} (ha1 : ((20637/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331041/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e221 e221_ok ha1 ha2 hz1 hz2 hz

-- box ['331041/1024000', '33189/102400', '999/1000', '1']  interval_lower 1864780883/549755813888
noncomputable def e222 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1454964194934,0,true,307989903616,307989903680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨744059060618,0,false,-429360358528,-429360358464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1455875801744,0,true,308678586112,308678586176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨743147453808,0,false,-430708284864,-430708284800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1454608742366,0,true,307721256448,307721256512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨744414513186,0,false,-428835224256,-428835224192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099704708605,0,true,193063872,193063936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099318546947,0,false,-193097792,-193097728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511593869,0,false,-33920,-33856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1454786466725,0,true,307855586752,307855586816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨744236788827,0,false,-429097757248,-429097757120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1455875810454,0,true,308678592704,308678592768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨743147445098,0,false,-430708297792,-430708297728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨984009956408,0,false,-122029705024,-122029704960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨984715014442,0,false,-121242170432,-121242170368⟩
    { al := (331041/1024000), au := (33189/102400), zl := (999/1000), zu := 1,
      A := ⟨355452567158,356364173968⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307989903616,307989903680⟩ : DyadicInterval 40),(⟨-429360358528,-429360358464⟩ : DyadicInterval 40),(⟨703622493756,703622513086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨308678586112,308678586176⟩ : DyadicInterval 40),(⟨-430708284864,-430708284800⟩ : DyadicInterval 40),(⟨703316402552,703316421882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307721256448,307721256512⟩ : DyadicInterval 40),(⟨-428835224256,-428835224192⟩ : DyadicInterval 40),(⟨703741615730,703741635059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨308678586112,308678586176⟩ : DyadicInterval 40),(⟨-430708284864,-430708284800⟩ : DyadicInterval 40),(⟨703316402552,703316421882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,193080829⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193063872,193063936⟩ : DyadicInterval 40),(⟨-193097792,-193097728⟩ : DyadicInterval 40),(⟨762123366605,762123385934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33920,0⟩ : DyadicInterval 40),(⟨762123383616,762123419840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨355274838949,356364182678⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨307855586752,307855586816⟩ : DyadicInterval 40),(⟨-429097757248,-429097757120⟩ : DyadicInterval 40),(⟨703682071442,703682090793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨308678592704,308678592768⟩ : DyadicInterval 40),(⟨-430708297792,-430708297728⟩ : DyadicInterval 40),(⟨703316399628,703316418957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-122029705024,-121242170368⟩ : DyadicInterval 40),(⟨822744468800,823138255392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨307989903616,308678586176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-430708284864,-429360358464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e222_ok : ecellOkT e222 = true := by decide +kernel
theorem e222_pos {a z : ℝ} (ha1 : ((331041/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33189/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e222 e222_ok ha1 ha2 hz1 hz2 hz

-- box ['33189/102400', '332739/1024000', '999/1000', '1']  interval_lower 3822055887/1099511627776
noncomputable def e223 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1455875801743,0,true,308678586112,308678586176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨743147453809,0,false,-430708284864,-430708284800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1456787408552,0,true,309366837568,309366837632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨742235847000,0,false,-432057865728,-432057865664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1455519437568,0,true,308409418560,308409418624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨743503817984,0,false,-430181158464,-430181158400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099705287034,0,true,193642176,193642240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099317968518,0,false,-193676352,-193676288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511593666,0,false,-34112,-34048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1455697617762,0,true,308544009152,308544009216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨743325637790,0,false,-430444687296,-430444687232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1456787417264,0,true,309366844160,309366844224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨742235838288,0,false,-432057878592,-432057878528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨983418276391,0,false,-122691034432,-122691034368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨984125436073,0,false,-121900678080,-121900678016⟩
    { al := (33189/102400), au := (332739/1024000), zl := (999/1000), zu := 1,
      A := ⟨356364173967,357275780776⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨308678586112,308678586176⟩ : DyadicInterval 40),(⟨-430708284864,-430708284800⟩ : DyadicInterval 40),(⟨703316402552,703316421882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309366837568,309366837632⟩ : DyadicInterval 40),(⟨-432057865728,-432057865664⟩ : DyadicInterval 40),(⟨703009466796,703009486126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨308409418560,308409418624⟩ : DyadicInterval 40),(⟨-430181158464,-430181158400⟩ : DyadicInterval 40),(⟨703436159860,703436179190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309366837568,309366837632⟩ : DyadicInterval 40),(⟨-432057865728,-432057865664⟩ : DyadicInterval 40),(⟨703009466796,703009486126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,193659258⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193642176,193642240⟩ : DyadicInterval 40),(⟨-193676352,-193676288⟩ : DyadicInterval 40),(⟨762123366530,762123385859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34112,0⟩ : DyadicInterval 40),(⟨762123383616,762123419936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨356185989986,357275789488⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨308544009152,308544009216⟩ : DyadicInterval 40),(⟨-430444687296,-430444687232⟩ : DyadicInterval 40),(⟨703376297974,703376317304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309366844160,309366844224⟩ : DyadicInterval 40),(⟨-432057878592,-432057878528⟩ : DyadicInterval 40),(⟨703009463834,703009483164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-122691034432,-121900678016⟩ : DyadicInterval 40),(⟨823073722624,823468920096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨308678586112,309366837632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-432057865728,-430708284800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e223_ok : ecellOkT e223 = true := by decide +kernel
theorem e223_pos {a z : ℝ} (ha1 : ((33189/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((332739/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e223 e223_ok ha1 ha2 hz1 hz2 hz

-- box ['332739/1024000', '83397/256000', '999/1000', '1']  interval_lower 3915596783/1099511627776
noncomputable def e224 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1456787408551,0,true,309366837568,309366837632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨742235847001,0,false,-432057865728,-432057865664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1457699015361,0,true,310054658432,310054658496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨741324240191,0,false,-433409105088,-433409105024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1456430132770,0,true,309097150272,309097150336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨742593122782,0,false,-431528742272,-431528742208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099705866203,0,true,194221248,194221312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099317389349,0,false,-194255616,-194255552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511593462,0,false,-34368,-34304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1456608769321,0,true,309232001152,309232001216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨742414486231,0,false,-431793270208,-431793270144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1457699024071,0,true,310054665024,310054665088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨741324231481,0,false,-433409118016,-433409117952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨982825084747,0,false,-123354452928,-123354452864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨983534347247,0,false,-122561268992,-122561268928⟩
    { al := (332739/1024000), au := (83397/256000), zl := (999/1000), zu := 1,
      A := ⟨357275780775,358187387585⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309366837568,309366837632⟩ : DyadicInterval 40),(⟨-432057865728,-432057865664⟩ : DyadicInterval 40),(⟨703009466797,703009486126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310054658432,310054658496⟩ : DyadicInterval 40),(⟨-433409105088,-433409105024⟩ : DyadicInterval 40),(⟨702701686007,702701705337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309097150272,309097150336⟩ : DyadicInterval 40),(⟨-431528742272,-431528742208⟩ : DyadicInterval 40),(⟨703129861319,703129880649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310054658432,310054658496⟩ : DyadicInterval 40),(⟨-433409105088,-433409105024⟩ : DyadicInterval 40),(⟨702701686007,702701705337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,194238427⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194221248,194221312⟩ : DyadicInterval 40),(⟨-194255616,-194255552⟩ : DyadicInterval 40),(⟨762123366422,762123385751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34368,0⟩ : DyadicInterval 40),(⟨762123383616,762123420064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨357097141545,358187396295⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309232001152,309232001216⟩ : DyadicInterval 40),(⟨-431793270208,-431793270144⟩ : DyadicInterval 40),(⟨703069680756,703069700086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310054665024,310054665088⟩ : DyadicInterval 40),(⟨-433409118016,-433409117952⟩ : DyadicInterval 40),(⟨702701683051,702701702380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-123354452928,-122561268928⟩ : DyadicInterval 40),(⟨823404018080,823800629344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨309366837568,310054658496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-433409105088,-432057865664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e224_ok : ecellOkT e224 = true := by decide +kernel
theorem e224_pos {a z : ℝ} (ha1 : ((332739/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((83397/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e224 e224_ok ha1 ha2 hz1 hz2 hz

-- box ['83397/256000', '334437/1024000', '999/1000', '1']  interval_lower 501273373/137438953472
noncomputable def e225 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1457699015360,0,true,310054658432,310054658496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨741324240192,0,false,-433409105088,-433409105024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1458610622170,0,true,310742049344,310742049408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨740412633382,0,false,-434762007104,-434762007040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1457340827972,0,true,309784452032,309784452096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨741682427580,0,false,-432877979776,-432877979712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099706446114,0,true,194801024,194801088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099316809438,0,false,-194835648,-194835584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511593256,0,false,-34560,-34496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1457519919846,0,true,309919562176,309919562240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨741503335706,0,false,-433143507648,-433143507584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1458610630893,0,true,310742055936,310742056000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨740412624659,0,false,-434762020096,-434762020032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨982230381464,0,false,-124019964160,-124019964096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨982941748975,0,false,-123223945408,-123223945344⟩
    { al := (83397/256000), au := (334437/1024000), zl := (999/1000), zu := 1,
      A := ⟨358187387584,359098994394⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310054658432,310054658496⟩ : DyadicInterval 40),(⟨-433409105088,-433409105024⟩ : DyadicInterval 40),(⟨702701686008,702701705337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310742049344,310742049408⟩ : DyadicInterval 40),(⟨-434762007104,-434762007040⟩ : DyadicInterval 40),(⟨702393059635,702393078964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309784452032,309784452096⟩ : DyadicInterval 40),(⟨-432877979776,-432877979712⟩ : DyadicInterval 40),(⟨702822719676,702822739005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310742049344,310742049408⟩ : DyadicInterval 40),(⟨-434762007104,-434762007040⟩ : DyadicInterval 40),(⟨702393059635,702393078964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,194818338⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194801024,194801088⟩ : DyadicInterval 40),(⟨-194835648,-194835584⟩ : DyadicInterval 40),(⟨762123366344,762123385673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34560,0⟩ : DyadicInterval 40),(⟨762123383616,762123420160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨358008292070,359099003117⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨309919562176,309919562240⟩ : DyadicInterval 40),(⟨-433143507648,-433143507584⟩ : DyadicInterval 40),(⟨702762219757,702762239086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310742055936,310742056000⟩ : DyadicInterval 40),(⟨-434762020096,-434762020032⟩ : DyadicInterval 40),(⟨702393056680,702393076009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-124019964160,-123223945344⟩ : DyadicInterval 40),(⟨823735356288,824133384960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨310054658432,310742049408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-434762007104,-433409105024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e225_ok : ecellOkT e225 = true := by decide +kernel
theorem e225_pos {a z : ℝ} (ha1 : ((83397/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((334437/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e225 e225_ok ha1 ha2 hz1 hz2 hz

-- box ['334437/1024000', '167643/512000', '999/1000', '1']  interval_lower 1026460321/274877906944
noncomputable def e226 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1458610622169,0,true,310742049344,310742049408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨740412633383,0,false,-434762007104,-434762007040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1459522228978,0,true,311429010752,311429010816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨739501026574,0,false,-436116575872,-436116575808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1458251523174,0,true,310471324480,310471324544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨740771732378,0,false,-434228874944,-434228874880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099707026770,0,true,195381632,195381696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099316228782,0,false,-195416384,-195416320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511593050,0,false,-34752,-34688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1458431070899,0,true,310606693888,310606693952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨740592184653,0,false,-434495406080,-434495406016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1459522237705,0,true,311429017280,311429017344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨739501017847,0,false,-436116588864,-436116588800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨981634166558,0,false,-124687571520,-124687571456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨982347640241,0,false,-123888712128,-123888712064⟩
    { al := (334437/1024000), au := (167643/512000), zl := (999/1000), zu := 1,
      A := ⟨359098994393,360010601202⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310742049344,310742049408⟩ : DyadicInterval 40),(⟨-434762007104,-434762007040⟩ : DyadicInterval 40),(⟨702393059635,702393078965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311429010752,311429010816⟩ : DyadicInterval 40),(⟨-436116575872,-436116575808⟩ : DyadicInterval 40),(⟨702083587226,702083606555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310471324480,310471324544⟩ : DyadicInterval 40),(⟨-434228874944,-434228874880⟩ : DyadicInterval 40),(⟨702514734323,702514753653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311429010752,311429010816⟩ : DyadicInterval 40),(⟨-436116575872,-436116575808⟩ : DyadicInterval 40),(⟨702083587226,702083606555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,195398994⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195381632,195381696⟩ : DyadicInterval 40),(⟨-195416384,-195416320⟩ : DyadicInterval 40),(⟨762123366202,762123385531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34752,0⟩ : DyadicInterval 40),(⟨762123383616,762123420256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨358919443123,360010609929⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨310606693888,310606693952⟩ : DyadicInterval 40),(⟨-434495406080,-434495406016⟩ : DyadicInterval 40),(⟨702453914002,702453933332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311429017280,311429017344⟩ : DyadicInterval 40),(⟨-436116588864,-436116588800⟩ : DyadicInterval 40),(⟨702083584296,702083603625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-124687571520,-123888712064⟩ : DyadicInterval 40),(⟨824067739648,824467188640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨310742049344,311429010816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-436116575872,-434762007040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e226_ok : ecellOkT e226 = true := by decide +kernel
theorem e226_pos {a z : ℝ} (ha1 : ((334437/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((167643/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e226 e226_ok ha1 ha2 hz1 hz2 hz

-- box ['167643/512000', '67227/204800', '999/1000', '1']  interval_lower 2101283321/549755813888
noncomputable def e227 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1459522228977,0,true,311429010752,311429010816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨739501026575,0,false,-436116575872,-436116575808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1460433835787,0,true,312115543232,312115543296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨738589419765,0,false,-437472815488,-437472815424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1459162218375,0,true,311157768064,311157768128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨739861037177,0,false,-435581431936,-435581431872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099707608175,0,true,195962880,195962944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099315647377,0,false,-195997888,-195997824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511592843,0,false,-34944,-34880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1459342221940,0,true,311293396480,311293396544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨739681033612,0,false,-435848968768,-435848968704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1460433844519,0,true,312115549760,312115549824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨738589411033,0,false,-437472828544,-437472828480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨981036440021,0,false,-125357278720,-125357278656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨981752021397,0,false,-124555572288,-124555572224⟩
    { al := (167643/512000), au := (67227/204800), zl := (999/1000), zu := 1,
      A := ⟨360010601201,360922208011⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311429010752,311429010816⟩ : DyadicInterval 40),(⟨-436116575872,-436116575808⟩ : DyadicInterval 40),(⟨702083587227,702083606556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312115543232,312115543296⟩ : DyadicInterval 40),(⟨-437472815488,-437472815424⟩ : DyadicInterval 40),(⟨701773268234,701773287564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311157768064,311157768128⟩ : DyadicInterval 40),(⟨-435581431936,-435581431872⟩ : DyadicInterval 40),(⟨702205904838,702205924167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312115543232,312115543296⟩ : DyadicInterval 40),(⟨-437472815488,-437472815424⟩ : DyadicInterval 40),(⟨701773268234,701773287564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,195980399⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195962880,195962944⟩ : DyadicInterval 40),(⟨-195997888,-195997824⟩ : DyadicInterval 40),(⟨762123366123,762123385452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34944,0⟩ : DyadicInterval 40),(⟨762123383616,762123420352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨359830594164,360922216743⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311293396480,311293396544⟩ : DyadicInterval 40),(⟨-435848968768,-435848968704⟩ : DyadicInterval 40),(⟨702144763114,702144782444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312115549760,312115549824⟩ : DyadicInterval 40),(⟨-437472828544,-437472828480⟩ : DyadicInterval 40),(⟨701773265307,701773284637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-125357278720,-124555572224⟩ : DyadicInterval 40),(⟨824401169728,824802042240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨311429010752,312115543296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-437472815488,-436116575808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e227_ok : ecellOkT e227 = true := by decide +kernel
theorem e227_pos {a z : ℝ} (ha1 : ((167643/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67227/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e227 e227_ok ha1 ha2 hz1 hz2 hz

-- box ['67227/204800', '42123/128000', '999/1000', '1']  interval_lower 4300371193/1099511627776
noncomputable def e228 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1460433835786,0,true,312115543168,312115543232⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨738589419766,0,false,-437472815488,-437472815424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1461345442595,0,true,312801647232,312801647296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨737677812957,0,false,-438830730112,-438830730048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1460072913577,0,true,311843783424,311843783488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨738950341975,0,false,-436935654784,-436935654720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099708190331,0,true,196544960,196545024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099315065221,0,false,-196580160,-196580096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511592636,0,false,-35200,-35136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1460253372987,0,true,311979670400,311979670464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨738769882565,0,false,-437204199808,-437204199744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1461345451306,0,true,312801653824,312801653888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨737677804246,0,false,-438830743104,-438830743040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨980437201873,0,false,-126029089216,-126029089152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨981154892431,0,false,-125224529344,-125224529280⟩
    { al := (67227/204800), au := (42123/128000), zl := (999/1000), zu := 1,
      A := ⟨360922208010,361833814819⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312115543168,312115543232⟩ : DyadicInterval 40),(⟨-437472815488,-437472815424⟩ : DyadicInterval 40),(⟨701773268277,701773287607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312801647232,312801647296⟩ : DyadicInterval 40),(⟨-438830730112,-438830730048⟩ : DyadicInterval 40),(⟨701462102214,701462121544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311843783424,311843783488⟩ : DyadicInterval 40),(⟨-436935654784,-436935654720⟩ : DyadicInterval 40),(⟨701896230616,701896249945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312801647232,312801647296⟩ : DyadicInterval 40),(⟨-438830730112,-438830730048⟩ : DyadicInterval 40),(⟨701462102214,701462121544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,196562555⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196544960,196545024⟩ : DyadicInterval 40),(⟨-196580160,-196580096⟩ : DyadicInterval 40),(⟨762123366011,762123385341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35200,0⟩ : DyadicInterval 40),(⟨762123383616,762123420480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨360741745211,361833823530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨311979670400,311979670464⟩ : DyadicInterval 40),(⟨-437204199808,-437204199744⟩ : DyadicInterval 40),(⟨701834766630,701834785959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312801653824,312801653888⟩ : DyadicInterval 40),(⟨-438830743104,-438830743040⟩ : DyadicInterval 40),(⟨701462099215,701462118544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-126029089216,-125224529280⟩ : DyadicInterval 40),(⟨824735648256,825137947488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨312115543168,312801647296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-438830730112,-437472815424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e228_ok : ecellOkT e228 = true := by decide +kernel
theorem e228_pos {a z : ℝ} (ha1 : ((67227/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((42123/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e228 e228_ok ha1 ha2 hz1 hz2 hz

-- box ['42123/128000', '337833/1024000', '999/1000', '1']  interval_lower 4399264185/1099511627776
noncomputable def e229 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1461345442594,0,true,312801647232,312801647296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨737677812958,0,false,-438830730112,-438830730048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1462257049404,0,true,313487323456,313487323520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨736766206148,0,false,-440190323840,-440190323776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1460983608779,0,true,312529370944,312529371008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨738039646773,0,false,-438291547648,-438291547584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099708773242,0,true,197127744,197127808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099314482310,0,false,-197163200,-197163136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511592427,0,false,-35392,-35328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1461164524025,0,true,312665516288,312665516352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨737858731527,0,false,-438561103360,-438561103296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1462257058123,0,true,313487330048,313487330112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨736766197429,0,false,-440190336832,-440190336768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨979836452076,0,false,-126703006784,-126703006720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨980556253353,0,false,-125895587008,-125895586944⟩
    { al := (42123/128000), au := (337833/1024000), zl := (999/1000), zu := 1,
      A := ⟨361833814818,362745421628⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312801647232,312801647296⟩ : DyadicInterval 40),(⟨-438830730112,-438830730048⟩ : DyadicInterval 40),(⟨701462102215,701462121544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313487323456,313487323520⟩ : DyadicInterval 40),(⟨-440190323840,-440190323776⟩ : DyadicInterval 40),(⟨701150088519,701150107849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312529370944,312529371008⟩ : DyadicInterval 40),(⟨-438291547648,-438291547584⟩ : DyadicInterval 40),(⟨701585711262,701585730591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313487323456,313487323520⟩ : DyadicInterval 40),(⟨-440190323840,-440190323776⟩ : DyadicInterval 40),(⟨701150088519,701150107849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,197145466⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197127744,197127808⟩ : DyadicInterval 40),(⟨-197163200,-197163136⟩ : DyadicInterval 40),(⟨762123365931,762123385260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35392,0⟩ : DyadicInterval 40),(⟨762123383616,762123420576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨361652896249,362745430347⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨312665516288,312665516352⟩ : DyadicInterval 40),(⟨-438561103360,-438561103296⟩ : DyadicInterval 40),(⟨701523923983,701523943313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313487330048,313487330112⟩ : DyadicInterval 40),(⟨-440190336832,-440190336768⟩ : DyadicInterval 40),(⟨701150085500,701150104830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-126703006784,-125895586944⟩ : DyadicInterval 40),(⟨825071177088,825474906272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨312801647232,313487323520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-440190323840,-438830730048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e229_ok : ecellOkT e229 = true := by decide +kernel
theorem e229_pos {a z : ℝ} (ha1 : ((42123/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((337833/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e229 e229_ok ha1 ha2 hz1 hz2 hz

-- box ['337833/1024000', '169341/512000', '999/1000', '1']  interval_lower 4499254263/1099511627776
noncomputable def e230 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1462257049403,0,true,313487323456,313487323520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨736766206149,0,false,-440190323840,-440190323776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1463168656212,0,true,314172572352,314172572416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨735854599340,0,false,-441551600832,-441551600768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1461894303981,0,true,313214531264,313214531328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨737128951571,0,false,-439649114624,-439649114560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099709356913,0,true,197711296,197711360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099313898639,0,false,-197746944,-197746880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511592217,0,false,-35584,-35520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1462075675073,0,true,313350934592,313350934656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨736947580479,0,false,-439919683520,-439919683456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1463168664942,0,true,314172578880,314172578944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨735854590610,0,false,-441551613888,-441551613824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨979234190648,0,false,-127379034944,-127379034880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨979956104150,0,false,-126568748864,-126568748800⟩
    { al := (337833/1024000), au := (169341/512000), zl := (999/1000), zu := 1,
      A := ⟨362745421627,363657028436⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313487323456,313487323520⟩ : DyadicInterval 40),(⟨-440190323840,-440190323776⟩ : DyadicInterval 40),(⟨701150088519,701150107849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314172572352,314172572416⟩ : DyadicInterval 40),(⟨-441551600832,-441551600768⟩ : DyadicInterval 40),(⟨700837226687,700837246016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313214531264,313214531328⟩ : DyadicInterval 40),(⟨-439649114624,-439649114560⟩ : DyadicInterval 40),(⟨701274346180,701274365510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314172572352,314172572416⟩ : DyadicInterval 40),(⟨-441551600832,-441551600768⟩ : DyadicInterval 40),(⟨700837226687,700837246016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,197729137⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197711296,197711360⟩ : DyadicInterval 40),(⟨-197746944,-197746880⟩ : DyadicInterval 40),(⟨762123365817,762123385146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35584,0⟩ : DyadicInterval 40),(⟨762123383616,762123420672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨362564047297,363657037166⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313350934592,313350934656⟩ : DyadicInterval 40),(⟨-439919683520,-439919683456⟩ : DyadicInterval 40),(⟨701212234697,701212254026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314172578880,314172578944⟩ : DyadicInterval 40),(⟨-441551613888,-441551613824⟩ : DyadicInterval 40),(⟨700837223712,700837243041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-127379034944,-126568748800⟩ : DyadicInterval 40),(⟨825407758016,825812920352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨313487323456,314172572416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-441551600832,-440190323776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e230_ok : ecellOkT e230 = true := by decide +kernel
theorem e230_pos {a z : ℝ} (ha1 : ((337833/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169341/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e230 e230_ok ha1 ha2 hz1 hz2 hz

-- box ['169341/512000', '339531/1024000', '999/1000', '1']  interval_lower 4600350777/1099511627776
noncomputable def e231 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1463168656211,0,true,314172572352,314172572416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨735854599341,0,false,-441551600832,-441551600768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1464080263021,0,true,314857394368,314857394432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨734942992531,0,false,-442914565312,-442914565184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1462804999182,0,true,313899264896,313899264960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨736218256370,0,false,-441008359872,-441008359808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099709941344,0,true,198295680,198295744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099313314208,0,false,-198331456,-198331392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511592007,0,false,-35776,-35712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1462986826122,0,true,314035925952,314035926016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨736036429430,0,false,-441279944448,-441279944384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1464080271744,0,true,314857400960,314857401024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨734942983808,0,false,-442914578304,-442914578240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨978630417603,0,false,-128057177344,-128057177280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨979354444828,0,false,-127244018496,-127244018432⟩
    { al := (169341/512000), au := (339531/1024000), zl := (999/1000), zu := 1,
      A := ⟨363657028435,364568635245⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314172572352,314172572416⟩ : DyadicInterval 40),(⟨-441551600832,-441551600768⟩ : DyadicInterval 40),(⟨700837226687,700837246016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314857394368,314857394432⟩ : DyadicInterval 40),(⟨-442914565312,-442914565184⟩ : DyadicInterval 40),(⟨700523516247,700523535598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨313899264896,313899264960⟩ : DyadicInterval 40),(⟨-441008359872,-441008359808⟩ : DyadicInterval 40),(⟨700962134874,700962154204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314857394368,314857394432⟩ : DyadicInterval 40),(⟨-442914565312,-442914565184⟩ : DyadicInterval 40),(⟨700523516247,700523535598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,198313568⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198295680,198295744⟩ : DyadicInterval 40),(⟨-198331456,-198331392⟩ : DyadicInterval 40),(⟨762123365670,762123385000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35776,0⟩ : DyadicInterval 40),(⟨762123383616,762123420768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨363475198346,364568643968⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314035925952,314035926016⟩ : DyadicInterval 40),(⟨-441279944448,-441279944384⟩ : DyadicInterval 40),(⟨700899698187,700899717516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314857400960,314857401024⟩ : DyadicInterval 40),(⟨-442914578304,-442914578240⟩ : DyadicInterval 40),(⟨700523513215,700523532545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128057177344,-127244018432⟩ : DyadicInterval 40),(⟨825745392832,826151991552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨314172572352,314857394432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-442914565312,-441551600768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e231_ok : ecellOkT e231 = true := by decide +kernel
theorem e231_pos {a z : ℝ} (ha1 : ((169341/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((339531/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e231 e231_ok ha1 ha2 hz1 hz2 hz

-- box ['339531/1024000', '17019/51200', '999/1000', '1']  interval_lower 4702562239/1099511627776
noncomputable def e232 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1464080263020,0,true,314857394368,314857394432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨734942992532,0,false,-442914565248,-442914565184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1464991869830,0,true,315541790144,315541790208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨734031385722,0,false,-444279221376,-444279221312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1463715694384,0,true,314583572416,314583572480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨735307561168,0,false,-442369287552,-442369287424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099710526541,0,true,198880768,198880832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099312729011,0,false,-198916800,-198916736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511591795,0,false,-36032,-35968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1463897977169,0,true,314720490752,314720490816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨735125278383,0,false,-442641890304,-442641890240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1464991878544,0,true,315541796736,315541796800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨734031377008,0,false,-444279234432,-444279234368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨978025132929,0,false,-128737437696,-128737437632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨978751275389,0,false,-127921399488,-127921399424⟩
    { al := (339531/1024000), au := (17019/51200), zl := (999/1000), zu := 1,
      A := ⟨364568635244,365480242054⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314857394368,314857394432⟩ : DyadicInterval 40),(⟨-442914565248,-442914565184⟩ : DyadicInterval 40),(⟨700523516247,700523535576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315541790144,315541790208⟩ : DyadicInterval 40),(⟨-444279221376,-444279221312⟩ : DyadicInterval 40),(⟨700208956637,700208975966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314583572416,314583572480⟩ : DyadicInterval 40),(⟨-442369287552,-442369287424⟩ : DyadicInterval 40),(⟨700649076774,700649096125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315541790144,315541790208⟩ : DyadicInterval 40),(⟨-444279221376,-444279221312⟩ : DyadicInterval 40),(⟨700208956637,700208975966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,198898765⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198880768,198880832⟩ : DyadicInterval 40),(⟨-198916800,-198916736⟩ : DyadicInterval 40),(⟨762123365587,762123384916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36032,0⟩ : DyadicInterval 40),(⟨762123383616,762123420896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨364386349393,365480250768⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨314720490752,314720490816⟩ : DyadicInterval 40),(⟨-442641890304,-442641890240⟩ : DyadicInterval 40),(⟨700586314032,700586333361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315541796736,315541796800⟩ : DyadicInterval 40),(⟨-444279234432,-444279234368⟩ : DyadicInterval 40),(⟨700208953593,700208972922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128737437696,-127921399424⟩ : DyadicInterval 40),(⟨826084083328,826492121728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨314857394368,315541790208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-444279221376,-442914565184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e232_ok : ecellOkT e232 = true := by decide +kernel
theorem e232_pos {a z : ℝ} (ha1 : ((339531/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17019/51200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e232 e232_ok ha1 ha2 hz1 hz2 hz

-- box ['17019/51200', '341229/1024000', '999/1000', '1']  interval_lower 150184321/34359738368
noncomputable def e233 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1464991869829,0,true,315541790144,315541790208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨734031385723,0,false,-444279221376,-444279221312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1465903476638,0,true,316225760192,316225760256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨733119778914,0,false,-445645573312,-445645573248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1464626389586,0,true,315267454272,315267454336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨734396865966,0,false,-443731901760,-443731901696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099711112506,0,true,199466624,199466688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099312143046,0,false,-199502848,-199502784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511591583,0,false,-36224,-36160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1464809128215,0,true,315404629632,315404629696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨734214127337,0,false,-444005525248,-444005525184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1465903485353,0,true,316225766784,316225766848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨733119770199,0,false,-445645586368,-445645586304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨977418336620,0,false,-129419819584,-129419819520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨978146595833,0,false,-128600895616,-128600895552⟩
    { al := (17019/51200), au := (341229/1024000), zl := (999/1000), zu := 1,
      A := ⟨365480242053,366391848862⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315541790144,315541790208⟩ : DyadicInterval 40),(⟨-444279221376,-444279221312⟩ : DyadicInterval 40),(⟨700208956637,700208975967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316225760192,316225760256⟩ : DyadicInterval 40),(⟨-445645573312,-445645573248⟩ : DyadicInterval 40),(⟨699893547308,699893566638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315267454272,315267454336⟩ : DyadicInterval 40),(⟨-443731901760,-443731901696⟩ : DyadicInterval 40),(⟨700335171453,700335190782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316225760192,316225760256⟩ : DyadicInterval 40),(⟨-445645573312,-445645573248⟩ : DyadicInterval 40),(⟨699893547308,699893566638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,199484730⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199466624,199466688⟩ : DyadicInterval 40),(⟨-199502848,-199502784⟩ : DyadicInterval 40),(⟨762123365471,762123384800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36224,0⟩ : DyadicInterval 40),(⟨762123383616,762123420992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨365297500439,366391857577⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315404629632,315404629696⟩ : DyadicInterval 40),(⟨-444005525248,-444005525184⟩ : DyadicInterval 40),(⟨700272081629,700272100959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316225766784,316225766848⟩ : DyadicInterval 40),(⟨-445645586368,-445645586304⟩ : DyadicInterval 40),(⟨699893544247,699893563577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-129419819584,-128600895552⟩ : DyadicInterval 40),(⟨826423831392,826833312672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨315541790144,316225760256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-445645573312,-444279221312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e233_ok : ecellOkT e233 = true := by decide +kernel
theorem e233_pos {a z : ℝ} (ha1 : ((17019/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((341229/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e233 e233_ok ha1 ha2 hz1 hz2 hz

-- box ['341229/1024000', '171039/512000', '999/1000', '1']  interval_lower 4910367401/1099511627776
noncomputable def e234 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1465903476637,0,true,316225760192,316225760256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨733119778915,0,false,-445645573312,-445645573248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1466815083447,0,true,316909305088,316909305152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨732208172105,0,false,-447013625280,-447013625216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1465537084788,0,true,315950910976,315950911040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨733486170764,0,false,-445096206784,-445096206720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099711699241,0,true,200053248,200053312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099311556311,0,false,-200089728,-200089664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511591370,0,false,-36416,-36352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1465720279254,0,true,316088343104,316088343168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨733302976298,0,false,-445370853568,-445370853504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1466815092184,0,true,316909311616,316909311680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨732208163368,0,false,-447013638400,-447013638336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨976810028667,0,false,-130104326784,-130104326720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨977540406164,0,false,-129282510400,-129282510336⟩
    { al := (341229/1024000), au := (171039/512000), zl := (999/1000), zu := 1,
      A := ⟨366391848861,367303455671⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316225760192,316225760256⟩ : DyadicInterval 40),(⟨-445645573312,-445645573248⟩ : DyadicInterval 40),(⟨699893547309,699893566638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316909305088,316909305152⟩ : DyadicInterval 40),(⟨-447013625280,-447013625216⟩ : DyadicInterval 40),(⟨699577287702,699577307032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨315950910976,315950911040⟩ : DyadicInterval 40),(⟨-445096206784,-445096206720⟩ : DyadicInterval 40),(⟨700020418370,700020437699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316909305088,316909305152⟩ : DyadicInterval 40),(⟨-447013625280,-447013625216⟩ : DyadicInterval 40),(⟨699577287702,699577307032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,200071465⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200053248,200053312⟩ : DyadicInterval 40),(⟨-200089728,-200089664⟩ : DyadicInterval 40),(⟨762123365385,762123384715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36416,0⟩ : DyadicInterval 40),(⟨762123383616,762123421088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨366208651478,367303464408⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316088343104,316088343168⟩ : DyadicInterval 40),(⟨-445370853568,-445370853504⟩ : DyadicInterval 40),(⟨699957000499,699957019829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316909311616,316909311680⟩ : DyadicInterval 40),(⟨-447013638400,-447013638336⟩ : DyadicInterval 40),(⟨699577284681,699577304011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-130104326784,-129282510336⟩ : DyadicInterval 40),(⟨826764638784,827175566272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨316225760192,316909305152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-447013625280,-445645573248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e234_ok : ecellOkT e234 = true := by decide +kernel
theorem e234_pos {a z : ℝ} (ha1 : ((341229/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171039/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e234 e234_ok ha1 ha2 hz1 hz2 hz

-- box ['171039/512000', '342927/1024000', '999/1000', '1']  interval_lower 5015979489/1099511627776
noncomputable def e235 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1466815083446,0,true,316909305088,316909305152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨732208172106,0,false,-447013625280,-447013625216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1467726690255,0,true,317592425216,317592425280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨731296565297,0,false,-448383381568,-448383381504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1466447779990,0,true,316633943168,316633943232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨732575475562,0,false,-446462206784,-446462206720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099712286753,0,true,200640640,200640704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099310968799,0,false,-200677312,-200677248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511591156,0,false,-36672,-36608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1466631430314,0,true,316771631680,316771631744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨732391825238,0,false,-446737879360,-446737879296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1467726698986,0,true,317592431744,317592431808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨731296556566,0,false,-448383394752,-448383394688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨976200209105,0,false,-130790962944,-130790962880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨976932706362,0,false,-129966247616,-129966247552⟩
    { al := (171039/512000), au := (342927/1024000), zl := (999/1000), zu := 1,
      A := ⟨367303455670,368215062479⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316909305088,316909305152⟩ : DyadicInterval 40),(⟨-447013625280,-447013625216⟩ : DyadicInterval 40),(⟨699577287703,699577307032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317592425216,317592425280⟩ : DyadicInterval 40),(⟨-448383381568,-448383381504⟩ : DyadicInterval 40),(⟨699260177404,699260196734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316633943168,316633943232⟩ : DyadicInterval 40),(⟨-446462206784,-446462206720⟩ : DyadicInterval 40),(⟨699704816933,699704836262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317592425216,317592425280⟩ : DyadicInterval 40),(⟨-448383381568,-448383381504⟩ : DyadicInterval 40),(⟨699260177404,699260196734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,200658977⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200640640,200640704⟩ : DyadicInterval 40),(⟨-200677312,-200677248⟩ : DyadicInterval 40),(⟨762123365267,762123384597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36672,0⟩ : DyadicInterval 40),(⟨762123383616,762123421216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨367119802538,368215071210⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨316771631680,316771631744⟩ : DyadicInterval 40),(⟨-446737879360,-446737879296⟩ : DyadicInterval 40),(⟨699641070079,699641089408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317592431744,317592431808⟩ : DyadicInterval 40),(⟨-448383394752,-448383394688⟩ : DyadicInterval 40),(⟨699260174391,699260193720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-130790962944,-129966247552⟩ : DyadicInterval 40),(⟨827106507392,827518884352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨316909305088,317592425280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-448383381568,-447013625216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e235_ok : ecellOkT e235 = true := by decide +kernel
theorem e235_pos {a z : ℝ} (ha1 : ((171039/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342927/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e235 e235_ok ha1 ha2 hz1 hz2 hz

-- box ['342927/1024000', '10743/32000', '999/1000', '1']  interval_lower 5122743747/1099511627776
noncomputable def e236 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1467726690254,0,true,317592425216,317592425280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨731296565298,0,false,-448383381568,-448383381504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1468638297064,0,true,318275121216,318275121280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨730384958488,0,false,-449754846464,-449754846400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1467358475191,0,true,317316551296,317316551360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨731664780361,0,false,-447829905920,-447829905856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099712875042,0,true,201228800,201228864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099310380510,0,false,-201265728,-201265664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511590941,0,false,-36864,-36800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1467542581359,0,true,317454495872,317454495936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨731480674193,0,false,-448106606912,-448106606848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1468638305789,0,true,318275127744,318275127808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨730384949763,0,false,-449754859584,-449754859520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨975588877912,0,false,-131479731776,-131479731712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨976323496452,0,false,-130652110976,-130652110912⟩
    { al := (342927/1024000), au := (10743/32000), zl := (999/1000), zu := 1,
      A := ⟨368215062478,369126669288⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317592425216,317592425280⟩ : DyadicInterval 40),(⟨-448383381568,-448383381504⟩ : DyadicInterval 40),(⟨699260177405,699260196734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318275121216,318275121280⟩ : DyadicInterval 40),(⟨-449754846464,-449754846400⟩ : DyadicInterval 40),(⟨698942215819,698942235149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317316551296,317316551360⟩ : DyadicInterval 40),(⟨-447829905920,-447829905856⟩ : DyadicInterval 40),(⟨699388366648,699388385977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318275121216,318275121280⟩ : DyadicInterval 40),(⟨-449754846464,-449754846400⟩ : DyadicInterval 40),(⟨698942215819,698942235149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,201247266⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201228800,201228864⟩ : DyadicInterval 40),(⟨-201265728,-201265664⟩ : DyadicInterval 40),(⟨762123365180,762123384510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36864,0⟩ : DyadicInterval 40),(⟨762123383616,762123421312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨368030953583,369126678013⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317454495872,317454495936⟩ : DyadicInterval 40),(⟨-448106606912,-448106606848⟩ : DyadicInterval 40),(⟨699324289884,699324309213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318275127744,318275127808⟩ : DyadicInterval 40),(⟨-449754859584,-449754859520⟩ : DyadicInterval 40),(⟨698942212770,698942232099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-131479731776,-130652110912⟩ : DyadicInterval 40),(⟨827449439072,827863268768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨317592425216,318275121280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-449754846464,-448383381504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e236_ok : ecellOkT e236 = true := by decide +kernel
theorem e236_pos {a z : ℝ} (ha1 : ((342927/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10743/32000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e236 e236_ok ha1 ha2 hz1 hz2 hz

-- box ['10743/32000', '2757/8192', '999/1000', '1']  interval_lower 653833649/137438953472
noncomputable def e237 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1468638297063,0,true,318275121216,318275121280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨730384958489,0,false,-449754846464,-449754846400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1469549903872,0,true,318957393600,318957393664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨729473351680,0,false,-451128024128,-451128024064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1468269170393,0,true,317998735872,317998735936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨730754085159,0,false,-449199308544,-449199308480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099713464113,0,true,201817792,201817856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099309791439,0,false,-201854912,-201854848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511590725,0,false,-37056,-36992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1468453732397,0,true,318136936256,318136936320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨730569523155,0,false,-449477040384,-449477040320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1469549912602,0,true,318957400128,318957400192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨729473342950,0,false,-451128037248,-451128037184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨974976035083,0,false,-132170637120,-132170637056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨975712776429,0,false,-131340104128,-131340104064⟩
    { al := (10743/32000), au := (2757/8192), zl := (999/1000), zu := 1,
      A := ⟨369126669287,370038276096⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318275121216,318275121280⟩ : DyadicInterval 40),(⟨-449754846464,-449754846400⟩ : DyadicInterval 40),(⟨698942215819,698942235149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318957393600,318957393664⟩ : DyadicInterval 40),(⟨-451128024128,-451128024064⟩ : DyadicInterval 40),(⟨698623402387,698623421717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨317998735872,317998735936⟩ : DyadicInterval 40),(⟨-449199308544,-449199308480⟩ : DyadicInterval 40),(⟨699071067035,699071086364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318957393600,318957393664⟩ : DyadicInterval 40),(⟨-451128024128,-451128024064⟩ : DyadicInterval 40),(⟨698623402387,698623421717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,201836337⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201817792,201817856⟩ : DyadicInterval 40),(⟨-201854912,-201854848⟩ : DyadicInterval 40),(⟨762123365060,762123384390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37056,0⟩ : DyadicInterval 40),(⟨762123383616,762123421408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨368942104621,370038284826⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318136936256,318136936320⟩ : DyadicInterval 40),(⟨-449477040384,-449477040320⟩ : DyadicInterval 40),(⟨699006659321,699006678651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318957400128,318957400192⟩ : DyadicInterval 40),(⟨-451128037248,-451128037184⟩ : DyadicInterval 40),(⟨698623399320,698623418649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-132170637120,-131340104064⟩ : DyadicInterval 40),(⟨827793435648,828208721440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨318275121216,318957393664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-451128024128,-449754846400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e237_ok : ecellOkT e237 = true := by decide +kernel
theorem e237_pos {a z : ℝ} (ha1 : ((10743/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2757/8192 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e237 e237_ok ha1 ha2 hz1 hz2 hz

-- box ['2757/8192', '172737/512000', '999/1000', '1']  interval_lower 5339765187/1099511627776
noncomputable def e238 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1469549903872,0,true,318957393600,318957393664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨729473351680,0,false,-451128024128,-451128024064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1470461510681,0,true,319639242880,319639242944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨728561744871,0,false,-452502918912,-452502918848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1469179865595,0,true,318680497536,318680497600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨729843389957,0,false,-450570418816,-450570418688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099714053968,0,true,202407552,202407616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099309201584,0,false,-202444864,-202444800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511590508,0,false,-37312,-37248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1469364883454,0,true,318818953280,318818953344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨729658372098,0,false,-450849184192,-450849184128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1470461519413,0,true,319639249408,319639249472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨728561736139,0,false,-452502932096,-452502932032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨974361680627,0,false,-132863682624,-132863682560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨975100546275,0,false,-132030230848,-132030230784⟩
    { al := (2757/8192), au := (172737/512000), zl := (999/1000), zu := 1,
      A := ⟨370038276096,370949882905⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318957393600,318957393664⟩ : DyadicInterval 40),(⟨-451128024128,-451128024064⟩ : DyadicInterval 40),(⟨698623402387,698623421717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨319639242880,319639242944⟩ : DyadicInterval 40),(⟨-452502918912,-452502918848⟩ : DyadicInterval 40),(⟨698303736605,698303755934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318680497536,318680497600⟩ : DyadicInterval 40),(⟨-450570418816,-450570418688⟩ : DyadicInterval 40),(⟨698752917436,698752936787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨319639242880,319639242944⟩ : DyadicInterval 40),(⟨-452502918912,-452502918848⟩ : DyadicInterval 40),(⟨698303736605,698303755934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,202426192⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202407552,202407616⟩ : DyadicInterval 40),(⟨-202444864,-202444800⟩ : DyadicInterval 40),(⟨762123364939,762123384269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37312,0⟩ : DyadicInterval 40),(⟨762123383616,762123421536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨369853255678,370949891637⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨318818953280,318818953344⟩ : DyadicInterval 40),(⟨-450849184192,-450849184128⟩ : DyadicInterval 40),(⟨698688177954,698688197283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨319639249408,319639249472⟩ : DyadicInterval 40),(⟨-452502932096,-452502932032⟩ : DyadicInterval 40),(⟨698303733542,698303752871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-132863682624,-132030230784⟩ : DyadicInterval 40),(⟨828138499008,828555244192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨318957393600,319639242944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-452502918912,-451128024064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e238_ok : ecellOkT e238 = true := by decide +kernel
theorem e238_pos {a z : ℝ} (ha1 : ((2757/8192 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((172737/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e238 e238_ok ha1 ha2 hz1 hz2 hz

-- box ['172737/512000', '346323/1024000', '999/1000', '1']  interval_lower 5450041815/1099511627776
noncomputable def e239 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1470461510680,0,true,319639242880,319639242944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨728561744872,0,false,-452502918912,-452502918848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1471373117490,0,true,320320669568,320320669632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨727650138062,0,false,-453879535040,-453879534976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1470090560797,0,true,319361836672,319361836736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨728932694755,0,false,-451943240960,-451943240896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099714644612,0,true,202998080,202998144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099308610940,0,false,-203035584,-203035520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511590290,0,false,-37504,-37440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1470276034506,0,true,319500547584,319500547648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨728747221046,0,false,-452223042496,-452223042368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1471373126229,0,true,320320676096,320320676160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨727650129323,0,false,-453879548288,-453879548224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨973745814538,0,false,-133558872128,-133558872064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨974486806005,0,false,-132722494848,-132722494784⟩
    { al := (172737/512000), au := (346323/1024000), zl := (999/1000), zu := 1,
      A := ⟨370949882904,371861489714⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨319639242880,319639242944⟩ : DyadicInterval 40),(⟨-452502918912,-452502918848⟩ : DyadicInterval 40),(⟨698303736605,698303755935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320320669568,320320669632⟩ : DyadicInterval 40),(⟨-453879535040,-453879534976⟩ : DyadicInterval 40),(⟨697983217918,697983237247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨319361836672,319361836736⟩ : DyadicInterval 40),(⟨-451943240960,-451943240896⟩ : DyadicInterval 40),(⟨698433917463,698433936793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320320669568,320320669632⟩ : DyadicInterval 40),(⟨-453879535040,-453879534976⟩ : DyadicInterval 40),(⟨697983217918,697983237247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,203016836⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202998080,202998144⟩ : DyadicInterval 40),(⟨-203035584,-203035520⟩ : DyadicInterval 40),(⟨762123364817,762123384147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37504,0⟩ : DyadicInterval 40),(⟨762123383616,762123421632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨370764406730,371861498453⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨319500547584,319500547648⟩ : DyadicInterval 40),(⟨-452223042496,-452223042368⟩ : DyadicInterval 40),(⟨698368845119,698368864470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320320676096,320320676160⟩ : DyadicInterval 40),(⟨-453879548288,-453879548224⟩ : DyadicInterval 40),(⟨697983214856,697983234186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-133558872128,-132722494784⟩ : DyadicInterval 40),(⟨828484631008,828902838944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨319639242880,320320669632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-453879535040,-452502918848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e239_ok : ecellOkT e239 = true := by decide +kernel
theorem e239_pos {a z : ℝ} (ha1 : ((172737/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((346323/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e239 e239_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B003

end


