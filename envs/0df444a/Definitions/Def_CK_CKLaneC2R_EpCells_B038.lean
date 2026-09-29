-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B038
-- name    : CK_CKLaneC2R_EpCells_B038
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:18:40.293472+00:00
-- url     : https://prove2.me/theorems/299eb1b4-ee42-488d-af1c-0bf38273cc35
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B038` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B038` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B038` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B038 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B038.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B038 =====
section

namespace CKLaneC2R.EpCells.B038

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['326727/2048000', '1307757/8192000', '1999/2000', '7997/8000']  interval_lower 105305053/549755813888
noncomputable def e2280 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274834145129,0,true,162672724864,162672724928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924189110423,0,false,-190990304256,-190990304192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274969979529,0,true,162789872320,162789872384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924053276023,0,false,-191151918912,-191151918848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545134422,0,true,33506112,33506176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478121130,0,false,-33507200,-33507136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556334130,0,true,44705408,44705472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466921422,0,false,-44707264,-44707200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625958,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626755,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274877993281,0,true,162710542144,162710542208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924145262271,0,false,-191042471808,-191042471744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275002898888,0,true,162818260992,162818261056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924020356664,0,false,-191191089664,-191191089600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071501750064,0,false,-28372828608,-28372828544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071541607839,0,false,-28331929664,-28331929600⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162672724864,162672724928⟩ : DyadicInterval 40),(⟨-190990304256,-190990304192⟩ : DyadicInterval 40),(⟨748085521664,748085540993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162789872320,162789872384⟩ : DyadicInterval 40),(⟨-191151918912,-191151918848⟩ : DyadicInterval 40),(⟨748063667169,748063686499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33506646,44706354⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33506112,33506176⟩ : DyadicInterval 40),(⟨-33507200,-33507136⟩ : DyadicInterval 40),(⟨762123383074,762123402403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44705408,44705472⟩ : DyadicInterval 40),(⟨-44707264,-44707200⟩ : DyadicInterval 40),(⟨762123382662,762123401991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175366365505,175491271112⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162710542144,162710542208⟩ : DyadicInterval 40),(⟨-191042471808,-191042471744⟩ : DyadicInterval 40),(⟨748078468763,748078488093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162818260992,162818261056⟩ : DyadicInterval 40),(⟨-191191089664,-191191089600⟩ : DyadicInterval 40),(⟨748058368179,748058387508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28372828608,-28331929600⟩ : DyadicInterval 40),(⟨776289348416,776309817184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2280_ok : ecellOkT e2280 = true := by decide +kernel
theorem e2280_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2280 e2280_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '1999/2000', '7997/8000']  interval_lower 211789037/1099511627776
noncomputable def e2281 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274948039005,0,true,162770951040,162770951104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924075216547,0,false,-191125812608,-191125812544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275083887648,0,true,162888100288,162888100352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923939367904,0,false,-191287464128,-191287464064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545157011,0,true,33528704,33528768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478098541,0,false,-33529792,-33529728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556364251,0,true,44735552,44735616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466891301,0,false,-44737408,-44737344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625955,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626754,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274991915640,0,true,162808789440,162808789504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924031339912,0,false,-191178020544,-191178020480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275116828379,0,true,162916504896,162916504960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923906427173,0,false,-191326665152,-191326665088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071465370055,0,false,-28410160256,-28410160192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071505255992,0,false,-28369231040,-28369230976⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162770951040,162770951104⟩ : DyadicInterval 40),(⟨-191125812608,-191125812544⟩ : DyadicInterval 40),(⟨748067198341,748067217671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162888100288,162888100352⟩ : DyadicInterval 40),(⟨-191287464128,-191287464064⟩ : DyadicInterval 40),(⟨748045327126,748045346455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33529235,44736475⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33528704,33528768⟩ : DyadicInterval 40),(⟨-33529792,-33529728⟩ : DyadicInterval 40),(⟨762123383073,762123402402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44735552,44735616⟩ : DyadicInterval 40),(⟨-44737408,-44737344⟩ : DyadicInterval 40),(⟨762123382659,762123401988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175480287864,175605200603⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162808789440,162808789504⟩ : DyadicInterval 40),(⟨-191178020544,-191178020480⟩ : DyadicInterval 40),(⟨748060136258,748060155588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162916504896,162916504960⟩ : DyadicInterval 40),(⟨-191326665152,-191326665088⟩ : DyadicInterval 40),(⟨748040021171,748040040501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28410160256,-28369230976⟩ : DyadicInterval 40),(⟨776307999104,776328483008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2281_ok : ecellOkT e2281 = true := by decide +kernel
theorem e2281_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2281 e2281_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '7997/8000', '3999/4000']  interval_lower 105224489/549755813888
noncomputable def e2282 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274856071407,0,true,162691635584,162691635648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924167184145,0,false,-191016390336,-191016390272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274991920050,0,true,162808793280,162808793344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924031335502,0,false,-191178025792,-191178025728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533965506,0,true,22337472,22337536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489290046,0,false,-22337984,-22337920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545157685,0,true,33529344,33529408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478097867,0,false,-33530432,-33530368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626753,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627323,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274888956334,0,true,162719997120,162719997184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924134299218,0,false,-191055515328,-191055515264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275013864989,0,true,162827717696,162827717760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924009390563,0,false,-191204138496,-191204138432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071498249391,0,false,-28376420800,-28376420736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071538110630,0,false,-28335518144,-28335518080⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162691635584,162691635648⟩ : DyadicInterval 40),(⟨-191016390336,-191016390272⟩ : DyadicInterval 40),(⟨748081995071,748082014400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162808793280,162808793344⟩ : DyadicInterval 40),(⟨-191178025792,-191178025728⟩ : DyadicInterval 40),(⟨748060135527,748060154857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22337730,33529909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22337472,22337536⟩ : DyadicInterval 40),(⟨-22337984,-22337920⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33529344,33529408⟩ : DyadicInterval 40),(⟨-33530432,-33530368⟩ : DyadicInterval 40),(⟨762123383073,762123402402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175377328558,175502237213⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162719997120,162719997184⟩ : DyadicInterval 40),(⟨-191055515328,-191055515264⟩ : DyadicInterval 40),(⟨748076705120,748076724449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162827717696,162827717760⟩ : DyadicInterval 40),(⟨-191204138496,-191204138432⟩ : DyadicInterval 40),(⟨748056602718,748056622048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28376420800,-28335518080⟩ : DyadicInterval 40),(⟨776291142656,776311613280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2282_ok : ecellOkT e2282 = true := by decide +kernel
theorem e2282_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2282 e2282_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '7997/8000', '3999/4000']  interval_lower 3306559/17179869184
noncomputable def e2283 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274969979526,0,true,162789872320,162789872384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924053276026,0,false,-191151918912,-191151918848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275105842414,0,true,162907031808,162907031872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923917413138,0,false,-191313591168,-191313591104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533980566,0,true,22352512,22352576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489274986,0,false,-22353024,-22352960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545180275,0,true,33551936,33552000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478075277,0,false,-33553024,-33552960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626752,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627322,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275002885810,0,true,162818249728,162818249792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924020369742,0,false,-191191074112,-191191074048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275127805696,0,true,162925970368,162925970432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923895449856,0,false,-191339728960,-191339728896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071461863527,0,false,-28413758592,-28413758528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071501754240,0,false,-28372824320,-28372824256⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162789872320,162789872384⟩ : DyadicInterval 40),(⟨-191151918912,-191151918848⟩ : DyadicInterval 40),(⟨748063667170,748063686499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162907031808,162907031872⟩ : DyadicInterval 40),(⟨-191313591168,-191313591104⟩ : DyadicInterval 40),(⟨748041790871,748041810201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22352790,33552499⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22352512,22352576⟩ : DyadicInterval 40),(⟨-22353024,-22352960⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33551936,33552000⟩ : DyadicInterval 40),(⟨-33553024,-33552960⟩ : DyadicInterval 40),(⟨762123383072,762123402401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175491258034,175616177920⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162818249728,162818249792⟩ : DyadicInterval 40),(⟨-191191074112,-191191074048⟩ : DyadicInterval 40),(⟨748058370280,748058389610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162925970368,162925970432⟩ : DyadicInterval 40),(⟨-191339728960,-191339728896⟩ : DyadicInterval 40),(⟨748038252780,748038272110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28413758592,-28372824256⟩ : DyadicInterval 40),(⟨776309795744,776330282176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2283_ok : ecellOkT e2283 = true := by decide +kernel
theorem e2283_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2283 e2283_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '1999/2000', '7997/8000']  interval_lower 106485687/549755813888
noncomputable def e2284 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275061932880,0,true,162869168384,162869168448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923961322672,0,false,-191261337728,-191261337664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275197795767,0,true,162986319488,162986319552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923825459785,0,false,-191423026112,-191423026048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545179601,0,true,33551296,33551360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478075951,0,false,-33552384,-33552320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556394373,0,true,44765632,44765696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466861179,0,false,-44767552,-44767488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625953,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626753,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275105838001,0,true,162907028032,162907028096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923917417551,0,false,-191313585920,-191313585856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275230757860,0,true,163014739968,163014740032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923792497692,0,false,-191462257344,-191462257280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071428966440,0,false,-28447517376,-28447517312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071468880537,0,false,-28406557888,-28406557824⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162869168384,162869168448⟩ : DyadicInterval 40),(⟨-191261337728,-191261337664⟩ : DyadicInterval 40),(⟨748048862973,748048882302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162986319488,162986319552⟩ : DyadicInterval 40),(⟨-191423026112,-191423026048⟩ : DyadicInterval 40),(⟨748026974993,748026994322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33551825,44766597⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33551296,33551360⟩ : DyadicInterval 40),(⟨-33552384,-33552320⟩ : DyadicInterval 40),(⟨762123383072,762123402401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44765632,44765696⟩ : DyadicInterval 40),(⟨-44767552,-44767488⟩ : DyadicInterval 40),(⟨762123382689,762123402018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175594210225,175719130084⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162907028032,162907028096⟩ : DyadicInterval 40),(⟨-191313585920,-191313585856⟩ : DyadicInterval 40),(⟨748041791566,748041810896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163014739968,163014740032⟩ : DyadicInterval 40),(⟨-191462257344,-191462257280⟩ : DyadicInterval 40),(⟨748021662077,748021681406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28447517376,-28406557824⟩ : DyadicInterval 40),(⟨776326662528,776347161568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2284_ok : ecellOkT e2284 = true := by decide +kernel
theorem e2284_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2284 e2284_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '1999/2000', '7997/8000']  interval_lower 214156137/1099511627776
noncomputable def e2285 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275175826756,0,true,162967377024,162967377088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923847428796,0,false,-191396879488,-191396879424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275311703887,0,true,163084529856,163084529920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923711551665,0,false,-191558604736,-191558604672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545202193,0,true,33573888,33573952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478053359,0,false,-33574976,-33574912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556424498,0,true,44795776,44795840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466831054,0,false,-44797696,-44797632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625950,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626751,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275219760363,0,true,163005257792,163005257856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923803495189,0,false,-191449168064,-191449168000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275344687346,0,true,163112966272,163112966336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923678568206,0,false,-191597866304,-191597866240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071392539212,0,false,-28484900032,-28484899968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071432481474,0,false,-28443910208,-28443910144⟩
    { al := (261891/1638400), au := (40947/256000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162967377024,162967377088⟩ : DyadicInterval 40),(⟨-191396879488,-191396879424⟩ : DyadicInterval 40),(⟨748030515430,748030534760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163084529856,163084529920⟩ : DyadicInterval 40),(⟨-191558604736,-191558604672⟩ : DyadicInterval 40),(⟨748008610752,748008630081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33574417,44796722⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33573888,33573952⟩ : DyadicInterval 40),(⟨-33574976,-33574912⟩ : DyadicInterval 40),(⟨762123383070,762123402399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44795776,44795840⟩ : DyadicInterval 40),(⟨-44797696,-44797632⟩ : DyadicInterval 40),(⟨762123382686,762123402015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175708132587,175833059570⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163005257792,163005257856⟩ : DyadicInterval 40),(⟨-191449168064,-191449168000⟩ : DyadicInterval 40),(⟨748023434816,748023454145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163112966272,163112966336⟩ : DyadicInterval 40),(⟨-191597866304,-191597866240⟩ : DyadicInterval 40),(⟨748003290881,748003310210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28484900032,-28443910144⟩ : DyadicInterval 40),(⟨776345338688,776365852896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2285_ok : ecellOkT e2285 = true := by decide +kernel
theorem e2285_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2285 e2285_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '7997/8000', '3999/4000']  interval_lower 26600179/137438953472
noncomputable def e2286 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275083887646,0,true,162888100288,162888100352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923939367906,0,false,-191287464128,-191287464064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275219764777,0,true,163005261632,163005261696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923803490775,0,false,-191449173312,-191449173248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533995626,0,true,22367616,22367680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489259926,0,false,-22368128,-22368064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545202868,0,true,33574528,33574592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478052684,0,false,-33575616,-33575552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626750,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627321,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275116815299,0,true,162916493568,162916493632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923906440253,0,false,-191326649600,-191326649536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275241742303,0,true,163024210752,163024210816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923781513249,0,false,-191475331264,-191475331200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071425455359,0,false,-28451120512,-28451120448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071465374234,0,false,-28410155968,-28410155904⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162888100288,162888100352⟩ : DyadicInterval 40),(⟨-191287464128,-191287464064⟩ : DyadicInterval 40),(⟨748045327126,748045346456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163005261632,163005261696⟩ : DyadicInterval 40),(⟨-191449173312,-191449173248⟩ : DyadicInterval 40),(⟨748023434082,748023453412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22367850,33575092⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22367616,22367680⟩ : DyadicInterval 40),(⟨-22368128,-22368064⟩ : DyadicInterval 40),(⟨762123383352,762123402681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33574528,33574592⟩ : DyadicInterval 40),(⟨-33575616,-33575552⟩ : DyadicInterval 40),(⟨762123383070,762123402399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175605187523,175730114527⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162916493568,162916493632⟩ : DyadicInterval 40),(⟨-191326649600,-191326649536⟩ : DyadicInterval 40),(⟨748040023313,748040042642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163024210752,163024210816⟩ : DyadicInterval 40),(⟨-191475331264,-191475331200⟩ : DyadicInterval 40),(⟨748019891369,748019910699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28451120512,-28410155904⟩ : DyadicInterval 40),(⟨776328461568,776348963136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2286_ok : ecellOkT e2286 = true := by decide +kernel
theorem e2286_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2286 e2286_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '7997/8000', '3999/4000']  interval_lower 106992957/549755813888
noncomputable def e2287 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275197795765,0,true,162986319488,162986319552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923825459787,0,false,-191423026048,-191423025984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275333687140,0,true,163103482624,163103482688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923689568412,0,false,-191584772160,-191584772096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534010688,0,true,22382656,22382720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489244864,0,false,-22383168,-22383104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545225461,0,true,33597120,33597184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478030091,0,false,-33598208,-33598144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626749,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627321,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275230744779,0,true,163014728640,163014728704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923792510773,0,false,-191462241792,-191462241728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275355678910,0,true,163122442368,163122442432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923667576642,0,false,-191610950336,-191610950272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071389023577,0,false,-28488507904,-28488507840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071428970622,0,false,-28447513088,-28447513024⟩
    { al := (261891/1638400), au := (40947/256000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162986319488,162986319552⟩ : DyadicInterval 40),(⟨-191423026048,-191423025984⟩ : DyadicInterval 40),(⟨748026974966,748026994296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163103482624,163103482688⟩ : DyadicInterval 40),(⟨-191584772160,-191584772096⟩ : DyadicInterval 40),(⟨748005065207,748005084536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22382912,33597685⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22382656,22382720⟩ : DyadicInterval 40),(⟨-22383168,-22383104⟩ : DyadicInterval 40),(⟨762123383352,762123402681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33597120,33597184⟩ : DyadicInterval 40),(⟨-33598208,-33598144⟩ : DyadicInterval 40),(⟨762123383069,762123402398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175719117003,175844051134⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163014728640,163014728704⟩ : DyadicInterval 40),(⟨-191462241792,-191462241728⟩ : DyadicInterval 40),(⟨748021664221,748021683551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163122442368,163122442432⟩ : DyadicInterval 40),(⟨-191610950336,-191610950272⟩ : DyadicInterval 40),(⟨748001517856,748001537185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28488507904,-28447513024⟩ : DyadicInterval 40),(⟨776347140128,776367656832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2287_ok : ecellOkT e2287 = true := by decide +kernel
theorem e2287_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2287 e2287_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '3999/4000', '7999/8000']  interval_lower 3285503/17179869184
noncomputable def e2288 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274877997685,0,true,162710545920,162710545984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924145257867,0,false,-191042477056,-191042476992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275013860572,0,true,162827713920,162827713984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924009394980,0,false,-191204133248,-191204133184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522796539,0,true,11168704,11168768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500459013,0,false,-11168832,-11168768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533981187,0,true,22353152,22353216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489274365,0,false,-22353664,-22353600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627321,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274899919407,0,true,162729452032,162729452096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924123336145,0,false,-191068558976,-191068558912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275024839310,0,true,162837181376,162837181440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923998416242,0,false,-191217197312,-191217197248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071494745876,0,false,-28380015936,-28380015872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071534613196,0,false,-28339106944,-28339106880⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175410222465,175524173317⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162710545920,162710545984⟩ : DyadicInterval 40),(⟨-191042477056,-191042476992⟩ : DyadicInterval 40),(⟨748078468071,748078487401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162827713920,162827713984⟩ : DyadicInterval 40),(⟨-191204133248,-191204133184⟩ : DyadicInterval 40),(⟨748056603414,748056622743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11168763,22353411⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11168704,11168768⟩ : DyadicInterval 40),(⟨-11168832,-11168768⟩ : DyadicInterval 40),(⟨762123383502,762123402831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22353152,22353216⟩ : DyadicInterval 40),(⟨-22353664,-22353600⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175388291631,175513211534⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162729452032,162729452096⟩ : DyadicInterval 40),(⟨-191068558976,-191068558912⟩ : DyadicInterval 40),(⟨748074941340,748074960669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162837181376,162837181440⟩ : DyadicInterval 40),(⟨-191217197312,-191217197248⟩ : DyadicInterval 40),(⟨748054835861,748054855191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28380015936,-28339106880⟩ : DyadicInterval 40),(⟨776292937056,776313410848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2288_ok : ecellOkT e2288 = true := by decide +kernel
theorem e2288_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2288 e2288_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '3999/4000', '7999/8000']  interval_lower 26431311/137438953472
noncomputable def e2289 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274991920048,0,true,162808793280,162808793344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924031335504,0,false,-191178025792,-191178025728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275127797179,0,true,162925963072,162925963136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923895458373,0,false,-191339718848,-191339718784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522804069,0,true,11176192,11176256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500451483,0,false,-11176384,-11176320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533996248,0,true,22368192,22368256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489259304,0,false,-22368704,-22368640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627320,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275013856007,0,true,162827709952,162827710016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924009399545,0,false,-191204127808,-191204127744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275138783044,0,true,162935435840,162935435904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923884472508,0,false,-191352793024,-191352792960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071458356770,0,false,-28417357120,-28417357056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071498252260,0,false,-28376417856,-28376417792⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175524173316,175638124168⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162808793280,162808793344⟩ : DyadicInterval 40),(⟨-191178025792,-191178025728⟩ : DyadicInterval 40),(⟨748060135527,748060154857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162925963072,162925963136⟩ : DyadicInterval 40),(⟨-191339718848,-191339718784⟩ : DyadicInterval 40),(⟨748038254134,748038273464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11176293,22368472⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11176192,11176256⟩ : DyadicInterval 40),(⟨-11176384,-11176320⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22368192,22368256⟩ : DyadicInterval 40),(⟨-22368704,-22368640⟩ : DyadicInterval 40),(⟨762123383352,762123402681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175502228231,175627155268⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162827709952,162827710016⟩ : DyadicInterval 40),(⟨-191204127808,-191204127744⟩ : DyadicInterval 40),(⟨748056604164,748056623493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162935435840,162935435904⟩ : DyadicInterval 40),(⟨-191352793024,-191352792960⟩ : DyadicInterval 40),(⟨748036484266,748036503596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28417357120,-28376417792⟩ : DyadicInterval 40),(⟨776311592512,776332081440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2289_ok : ecellOkT e2289 = true := by decide +kernel
theorem e2289_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2289 e2289_ok ha1 ha2 hz1 hz2 hz

-- box ['326727/2048000', '1307757/8192000', '7999/8000', '1']  interval_lower 210103325/1099511627776
noncomputable def e2290 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274921850241,0,true,162748365696,162748365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924101405311,0,false,-191094652352,-191094652288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801093,0,true,162846634176,162846634240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454459,0,false,-191230241408,-191230241344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274899923963,0,true,162729455936,162729456000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924123331589,0,false,-191068564416,-191068564352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522804636,0,true,11176768,11176832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500450916,0,false,-11176960,-11176896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1274910882505,0,true,162738906880,162738906944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨924112373047,0,false,-191081602816,-191081602752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035809553,0,true,162846641472,162846641536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923987445999,0,false,-191230251456,-191230251392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071491243443,0,false,-28383609920,-28383609856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071531115536,0,false,-28342695872,-28342695808⟩
    { al := (326727/2048000), au := (1307757/8192000), zl := (7999/8000), zu := 1,
      A := ⟨175410222465,175524173317⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162748365696,162748365760⟩ : DyadicInterval 40),(⟨-191094652352,-191094652288⟩ : DyadicInterval 40),(⟨748071412681,748071432010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162729455936,162729456000⟩ : DyadicInterval 40),(⟨-191068564416,-191068564352⟩ : DyadicInterval 40),(⟨748074940630,748074959959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070920,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11176860⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11176768,11176832⟩ : DyadicInterval 40),(⟨-11176960,-11176896⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175399254729,175524181777⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162738906880,162738906944⟩ : DyadicInterval 40),(⟨-191081602816,-191081602752⟩ : DyadicInterval 40),(⟨748073177449,748073196778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846641472,162846641536⟩ : DyadicInterval 40),(⟨-191230251456,-191230251392⟩ : DyadicInterval 40),(⟨748053069550,748053088880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28383609920,-28342695808⟩ : DyadicInterval 40),(⟨776294731520,776315207840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162748365696,162846634240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191230241408,-191094652288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2290_ok : ecellOkT e2290 = true := by decide +kernel
theorem e2290_pos {a z : ℝ} (ha1 : ((326727/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1307757/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2290 e2290_ok ha1 ha2 hz1 hz2 hz

-- box ['1307757/8192000', '654303/4096000', '7999/8000', '1']  interval_lower 211281191/1099511627776
noncomputable def e2291 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275035801092,0,true,162846634176,162846634240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923987454460,0,false,-191230241408,-191230241344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751944,0,true,162944893952,162944894016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503608,0,false,-191365847104,-191365847040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275013860570,0,true,162827713920,162827713984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924009394982,0,false,-191204133248,-191204133184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522812167,0,true,11184320,11184384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500443385,0,false,-11184448,-11184384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275024826232,0,true,162837170112,162837170176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923998429320,0,false,-191217181760,-191217181696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149760413,0,true,162944901248,162944901312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923873495139,0,false,-191365857216,-191365857152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071454849787,0,false,-28420955968,-28420955904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071494750052,0,false,-28380011648,-28380011584⟩
    { al := (1307757/8192000), au := (654303/4096000), zl := (7999/8000), zu := 1,
      A := ⟨175524173316,175638124168⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162846634176,162846634240⟩ : DyadicInterval 40),(⟨-191230241408,-191230241344⟩ : DyadicInterval 40),(⟨748053070921,748053090250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162827713920,162827713984⟩ : DyadicInterval 40),(⟨-191204133248,-191204133184⟩ : DyadicInterval 40),(⟨748056603414,748056622744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11184391⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11184320,11184384⟩ : DyadicInterval 40),(⟨-11184448,-11184384⟩ : DyadicInterval 40),(⟨762123383502,762123402831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175513198456,175638132637⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162837170112,162837170176⟩ : DyadicInterval 40),(⟨-191217181760,-191217181696⟩ : DyadicInterval 40),(⟨748054837963,748054857292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944901248,162944901312⟩ : DyadicInterval 40),(⟨-191365857216,-191365857152⟩ : DyadicInterval 40),(⟨748034715615,748034734945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28420955968,-28380011584⟩ : DyadicInterval 40),(⟨776313389408,776333880864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162846634176,162944894016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191365847104,-191230241344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2291_ok : ecellOkT e2291 = true := by decide +kernel
theorem e2291_pos {a z : ℝ} (ha1 : ((1307757/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((654303/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2291 e2291_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '3999/4000', '7999/8000']  interval_lower 26578957/137438953472
noncomputable def e2292 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275105842411,0,true,162907031808,162907031872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923917413141,0,false,-191313591168,-191313591104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275241733786,0,true,163024203392,163024203456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923781521766,0,false,-191475321152,-191475321088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522811599,0,true,11183744,11183808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500443953,0,false,-11183936,-11183872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534011309,0,true,22383296,22383360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489244243,0,false,-22383808,-22383744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627320,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275127792616,0,true,162925959104,162925959168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923895462936,0,false,-191339713408,-191339713344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275252726766,0,true,163033681536,163033681600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923770528786,0,false,-191488405376,-191488405312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071421944052,0,false,-28454723840,-28454723776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071461867707,0,false,-28413754240,-28413754176⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175638124167,175752075019⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162907031808,162907031872⟩ : DyadicInterval 40),(⟨-191313591168,-191313591104⟩ : DyadicInterval 40),(⟨748041790872,748041810201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163024203392,163024203456⟩ : DyadicInterval 40),(⟨-191475321152,-191475321088⟩ : DyadicInterval 40),(⟨748019892763,748019912092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11183823,22383533⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11183744,11183808⟩ : DyadicInterval 40),(⟨-11183936,-11183872⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22383296,22383360⟩ : DyadicInterval 40),(⟨-22383808,-22383744⟩ : DyadicInterval 40),(⟨762123383352,762123402681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175616164840,175741098990⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162925959104,162925959168⟩ : DyadicInterval 40),(⟨-191339713408,-191339713344⟩ : DyadicInterval 40),(⟨748038254885,748038274214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163033681536,163033681600⟩ : DyadicInterval 40),(⟨-191488405376,-191488405312⟩ : DyadicInterval 40),(⟨748018120515,748018139844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28454723840,-28413754176⟩ : DyadicInterval 40),(⟨776330260704,776350764800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2292_ok : ecellOkT e2292 = true := by decide +kernel
theorem e2292_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2292 e2292_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '3999/4000', '7999/8000']  interval_lower 213815821/1099511627776
noncomputable def e2293 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275219764775,0,true,163005261632,163005261696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923803490777,0,false,-191449173312,-191449173248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275355670393,0,true,163122435008,163122435072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923667585159,0,false,-191610940160,-191610940096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522819129,0,true,11191296,11191360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500436423,0,false,-11191424,-11191360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534026372,0,true,22398336,22398400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489229180,0,false,-22398848,-22398784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627319,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275241729219,0,true,163024199488,163024199552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923781526333,0,false,-191475315712,-191475315648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275366670498,0,true,163131918400,163131918464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923656585054,0,false,-191624034496,-191624034432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071385507715,0,false,-28492116096,-28492116032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071425459542,0,false,-28451116224,-28451116160⟩
    { al := (261891/1638400), au := (40947/256000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175752075018,175866025870⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163005261632,163005261696⟩ : DyadicInterval 40),(⟨-191449173312,-191449173248⟩ : DyadicInterval 40),(⟨748023434082,748023453412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163122435008,163122435072⟩ : DyadicInterval 40),(⟨-191610940160,-191610940096⟩ : DyadicInterval 40),(⟨748001519224,748001538553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11191353,22398596⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11191296,11191360⟩ : DyadicInterval 40),(⟨-11191424,-11191360⟩ : DyadicInterval 40),(⟨762123383502,762123402831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22398336,22398400⟩ : DyadicInterval 40),(⟨-22398848,-22398784⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175730101443,175855042722⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163024199488,163024199552⟩ : DyadicInterval 40),(⟨-191475315712,-191475315648⟩ : DyadicInterval 40),(⟨748019893478,748019912807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163131918400,163131918464⟩ : DyadicInterval 40),(⟨-191624034496,-191624034432⟩ : DyadicInterval 40),(⟨747999744692,747999764022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28492116096,-28451116160⟩ : DyadicInterval 40),(⟨776348941696,776369460928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2293_ok : ecellOkT e2293 = true := by decide +kernel
theorem e2293_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2293 e2293_ok ha1 ha2 hz1 hz2 hz

-- box ['654303/4096000', '261891/1638400', '7999/8000', '1']  interval_lower 212462273/1099511627776
noncomputable def e2294 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275149751943,0,true,162944893952,162944894016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923873503609,0,false,-191365847104,-191365847040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702795,0,true,163043144896,163043144960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552757,0,false,-191501469632,-191501469568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275127797177,0,true,162925963072,162925963136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923895458375,0,false,-191339718848,-191339718784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522819698,0,true,11191808,11191872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500435854,0,false,-11192000,-11191936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275138769963,0,true,162935424576,162935424640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923884485589,0,false,-191352777408,-191352777344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263711257,0,true,163043152192,163043152256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923759544295,0,false,-191501479680,-191501479616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071418432517,0,false,-28458327424,-28458327360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071458360950,0,false,-28417352832,-28417352768⟩
    { al := (654303/4096000), au := (261891/1638400), zl := (7999/8000), zu := 1,
      A := ⟨175638124167,175752075019⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162944893952,162944894016⟩ : DyadicInterval 40),(⟨-191365847104,-191365847040⟩ : DyadicInterval 40),(⟨748034716963,748034736292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162925963072,162925963136⟩ : DyadicInterval 40),(⟨-191339718848,-191339718784⟩ : DyadicInterval 40),(⟨748038254135,748038273464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350959,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11191922⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11191808,11191872⟩ : DyadicInterval 40),(⟨-11192000,-11191936⟩ : DyadicInterval 40),(⟨762123383534,762123402863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175627142187,175752083481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162935424576,162935424640⟩ : DyadicInterval 40),(⟨-191352777408,-191352777344⟩ : DyadicInterval 40),(⟨748036486345,748036505674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043152192,163043152256⟩ : DyadicInterval 40),(⟨-191501479680,-191501479616⟩ : DyadicInterval 40),(⟨748016349585,748016368914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28458327424,-28417352768⟩ : DyadicInterval 40),(⟨776332060000,776352566592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨162944893952,163043144960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191501469632,-191365847040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2294_ok : ecellOkT e2294 = true := by decide +kernel
theorem e2294_pos {a z : ℝ} (ha1 : ((654303/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261891/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2294 e2294_ok ha1 ha2 hz1 hz2 hz

-- box ['261891/1638400', '40947/256000', '7999/8000', '1']  interval_lower 106822855/549755813888
noncomputable def e2295 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275263702794,0,true,163043144896,163043144960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923759552758,0,false,-191501469632,-191501469568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653646,0,true,163141387072,163141387136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601906,0,false,-191637108800,-191637108736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275241733784,0,true,163024203392,163024203456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923781521768,0,false,-191475321152,-191475321088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522827229,0,true,11199360,11199424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500428323,0,false,-11199552,-11199488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275252713682,0,true,163033670208,163033670272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923770541870,0,false,-191488389824,-191488389760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377662111,0,true,163141394368,163141394432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923645593441,0,false,-191637118912,-191637118848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071381991625,0,false,-28495724480,-28495724416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071421948236,0,false,-28454719552,-28454719488⟩
    { al := (261891/1638400), au := (40947/256000), zl := (7999/8000), zu := 1,
      A := ⟨175752075018,175866025870⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163043144896,163043144960⟩ : DyadicInterval 40),(⟨-191501469632,-191501469568⟩ : DyadicInterval 40),(⟨748016350960,748016370289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163024203392,163024203456⟩ : DyadicInterval 40),(⟨-191475321152,-191475321088⟩ : DyadicInterval 40),(⟨748019892763,748019912093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11199453⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11199360,11199424⟩ : DyadicInterval 40),(⟨-11199552,-11199488⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175741085906,175866034335⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163033670208,163033670272⟩ : DyadicInterval 40),(⟨-191488389824,-191488389760⟩ : DyadicInterval 40),(⟨748018122660,748018141990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141394368,163141394432⟩ : DyadicInterval 40),(⟨-191637118912,-191637118848⟩ : DyadicInterval 40),(⟨747997971443,747997990773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28495724480,-28454719488⟩ : DyadicInterval 40),(⟨776350743360,776371265120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163043144896,163141387136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191637108800,-191501469568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2295_ok : ecellOkT e2295 = true := by decide +kernel
theorem e2295_pos {a z : ℝ} (ha1 : ((261891/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40947/256000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2295 e2295_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '999/1000', '7993/8000']  interval_lower 108012427/549755813888
noncomputable def e2296 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275201787619,0,true,162989761344,162989761408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923821467933,0,false,-191427777088,-191427777024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275337622018,0,true,163106875008,163106875072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923685633534,0,false,-191589456000,-191589455936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590020400,0,true,78389824,78389888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433235152,0,false,-78395456,-78395392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601280365,0,true,89648896,89648960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421975187,0,false,-89656256,-89656192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620465,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622187,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275289716832,0,true,163065573568,163065573632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923733538720,0,false,-191532433472,-191532433408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275414622352,0,true,163173257600,163173257664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923608633200,0,false,-191681117376,-191681117312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071370166859,0,false,-28507859776,-28507859712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071410118150,0,false,-28466859840,-28466859776⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162989761344,162989761408⟩ : DyadicInterval 40),(⟨-191427777088,-191427777024⟩ : DyadicInterval 40),(⟨748026331636,748026350965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163106875008,163106875072⟩ : DyadicInterval 40),(⟨-191589456000,-191589455936⟩ : DyadicInterval 40),(⟨748004430518,748004449848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78392624,89652589⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78389824,78389888⟩ : DyadicInterval 40),(⟨-78395456,-78395392⟩ : DyadicInterval 40),(⟨762123380778,762123400107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89648896,89648960⟩ : DyadicInterval 40),(⟨-89656256,-89656192⟩ : DyadicInterval 40),(⟨762123379921,762123399251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175778089056,175902994576⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163065573568,163065573632⟩ : DyadicInterval 40),(⟨-191532433472,-191532433408⟩ : DyadicInterval 40),(⟨748012156436,748012175766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163173257600,163173257664⟩ : DyadicInterval 40),(⟨-191681117376,-191681117312⟩ : DyadicInterval 40),(⟨747992007809,747992027139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28507859776,-28466859776⟩ : DyadicInterval 40),(⟨776356813504,776377332768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2296_ok : ecellOkT e2296 = true := by decide +kernel
theorem e2296_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2296 e2296_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '999/1000', '7993/8000']  interval_lower 108608583/549755813888
noncomputable def e2297 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275315624519,0,true,163087910080,163087910144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923707631033,0,false,-191563271552,-191563271488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275451473162,0,true,163205025536,163205025600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923571782390,0,false,-191724987392,-191724987328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590073121,0,true,78442496,78442560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433182431,0,false,-78448192,-78448128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601340622,0,true,89709184,89709248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421914930,0,false,-89716544,-89716480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620456,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622180,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275403610709,0,true,163163764608,163163764672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923619644843,0,false,-191668008640,-191668008576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275528523349,0,true,163271445184,163271445248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923494732203,0,false,-191816719424,-191816719360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071333710649,0,false,-28545274240,-28545274176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071373690097,0,false,-28504244032,-28504243968⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163087910080,163087910144⟩ : DyadicInterval 40),(⟨-191563271552,-191563271488⟩ : DyadicInterval 40),(⟨748007978424,748007997753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163205025536,163205025600⟩ : DyadicInterval 40),(⟨-191724987392,-191724987328⟩ : DyadicInterval 40),(⟨747986060613,747986079942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78445345,89712846⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78442496,78442560⟩ : DyadicInterval 40),(⟨-78448192,-78448128⟩ : DyadicInterval 40),(⟨762123380803,762123400132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89709184,89709248⟩ : DyadicInterval 40),(⟨-89716544,-89716480⟩ : DyadicInterval 40),(⟨762123379911,762123399241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175891982933,176016895573⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163163764608,163163764672⟩ : DyadicInterval 40),(⟨-191668008640,-191668008576⟩ : DyadicInterval 40),(⟨747993784707,747993804037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163271445184,163271445248⟩ : DyadicInterval 40),(⟨-191816719424,-191816719360⟩ : DyadicInterval 40),(⟨747973621667,747973640997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28545274240,-28504243968⟩ : DyadicInterval 40),(⟨776375505600,776396040000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2297_ok : ecellOkT e2297 = true := by decide +kernel
theorem e2297_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2297 e2297_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '7993/8000', '3997/4000']  interval_lower 215855021/1099511627776
noncomputable def e2298 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275223770872,0,true,163008715712,163008715776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923799484680,0,false,-191453941376,-191453941312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275359619515,0,true,163125839616,163125839680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923663636037,0,false,-191615641152,-191615641088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578821576,0,true,67191744,67191808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444433976,0,false,-67195904,-67195840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590074009,0,true,78443392,78443456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433181543,0,false,-78449088,-78449024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622179,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623670,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275300708266,0,true,163075049984,163075050048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923722547286,0,false,-191545516544,-191545516480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275425620931,0,true,163182739200,163182739264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923597634621,0,false,-191694210752,-191694210688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071366647581,0,false,-28511471488,-28511471424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071406603656,0,false,-28470466560,-28470466496⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163008715712,163008715776⟩ : DyadicInterval 40),(⟨-191453941376,-191453941312⟩ : DyadicInterval 40),(⟨748022788356,748022807685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163125839616,163125839680⟩ : DyadicInterval 40),(⟨-191615641152,-191615641088⟩ : DyadicInterval 40),(⟨748000882191,748000901520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67193800,78446233⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67191744,67191808⟩ : DyadicInterval 40),(⟨-67195904,-67195840⟩ : DyadicInterval 40),(⟨762123381525,762123400854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78443392,78443456⟩ : DyadicInterval 40),(⟨-78449088,-78449024⟩ : DyadicInterval 40),(⟨762123380802,762123400132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175789080490,175913993155⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163075049984,163075050048⟩ : DyadicInterval 40),(⟨-191545516544,-191545516480⟩ : DyadicInterval 40),(⟨748010383971,748010403301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163182739200,163182739264⟩ : DyadicInterval 40),(⟨-191694210752,-191694210688⟩ : DyadicInterval 40),(⟨747990232949,747990252279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28511471488,-28470466496⟩ : DyadicInterval 40),(⟨776358616864,776379138624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2298_ok : ecellOkT e2298 = true := by decide +kernel
theorem e2298_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2298 e2298_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '7993/8000', '3997/4000']  interval_lower 108523377/549755813888
noncomputable def e2299 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275337622016,0,true,163106875008,163106875072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923685633536,0,false,-191589456000,-191589455936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275473484903,0,true,163224000768,163224000832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923549770649,0,false,-191751192640,-191751192576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578866766,0,true,67236928,67236992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444388786,0,false,-67241088,-67241024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590126735,0,true,78496128,78496192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433128817,0,false,-78501824,-78501760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622171,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623665,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275414609265,0,true,163173246336,163173246400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923608646287,0,false,-191681101824,-191681101760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275539529056,0,true,163280932096,163280932160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923483726496,0,false,-191829822848,-191829822784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071330186810,0,false,-28548890752,-28548890688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071370171047,0,false,-28507855488,-28507855424⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163106875008,163106875072⟩ : DyadicInterval 40),(⟨-191589456000,-191589455936⟩ : DyadicInterval 40),(⟨748004430519,748004449848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163224000768,163224000832⟩ : DyadicInterval 40),(⟨-191751192640,-191751192576⟩ : DyadicInterval 40),(⟨747982507589,747982526919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67238990,78498959⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67236928,67236992⟩ : DyadicInterval 40),(⟨-67241088,-67241024⟩ : DyadicInterval 40),(⟨762123381519,762123400849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78496128,78496192⟩ : DyadicInterval 40),(⟨-78501824,-78501760⟩ : DyadicInterval 40),(⟨762123380795,762123400124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175902981489,176027901280⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163173246336,163173246400⟩ : DyadicInterval 40),(⟨-191681101824,-191681101760⟩ : DyadicInterval 40),(⟨747992009922,747992029252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163280932096,163280932160⟩ : DyadicInterval 40),(⟨-191829822848,-191829822784⟩ : DyadicInterval 40),(⟨747971844456,747971863785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28548890752,-28507855424⟩ : DyadicInterval 40),(⟨776377311328,776397848256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2299_ok : ecellOkT e2299 = true := by decide +kernel
theorem e2299_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2299 e2299_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '999/1000', '7993/8000']  interval_lower 109206125/549755813888
noncomputable def e2300 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275429461419,0,true,163186049984,163186050048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923593794133,0,false,-191698782720,-191698782656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275565324306,0,true,163303167296,163303167360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923457931246,0,false,-191860535488,-191860535424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590125845,0,true,78495232,78495296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433129707,0,false,-78500928,-78500864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601400884,0,true,89769408,89769472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421854668,0,false,-89776832,-89776768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620446,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622172,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275517504581,0,true,163261946880,163261946944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923505750971,0,false,-191803600576,-191803600512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275642424348,0,true,163369624000,163369624064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923380831204,0,false,-191952338176,-191952338112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071297230840,0,false,-28582714112,-28582714048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071337238450,0,false,-28541653632,-28541653568⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163186049984,163186050048⟩ : DyadicInterval 40),(⟨-191698782720,-191698782656⟩ : DyadicInterval 40),(⟨747989613160,747989632489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163303167296,163303167360⟩ : DyadicInterval 40),(⟨-191860535488,-191860535424⟩ : DyadicInterval 40),(⟨747967678611,747967697940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78498069,89773108⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78495232,78495296⟩ : DyadicInterval 40),(⟨-78500928,-78500864⟩ : DyadicInterval 40),(⟨762123380795,762123400124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89769408,89769472⟩ : DyadicInterval 40),(⟨-89776832,-89776768⟩ : DyadicInterval 40),(⟨762123379933,762123399263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176005876805,176130796572⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163261946880,163261946944⟩ : DyadicInterval 40),(⟨-191803600576,-191803600512⟩ : DyadicInterval 40),(⟨747975400891,747975420221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163369624000,163369624064⟩ : DyadicInterval 40),(⟨-191952338176,-191952338112⟩ : DyadicInterval 40),(⟨747955223406,747955242735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28582714112,-28541653568⟩ : DyadicInterval 40),(⟨776394210400,776414759936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2300_ok : ecellOkT e2300 = true := by decide +kernel
theorem e2300_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2300 e2300_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '999/1000', '7993/8000']  interval_lower 219610191/1099511627776
noncomputable def e2301 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275543298319,0,true,163284181184,163284181248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923479957233,0,false,-191834310592,-191834310528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275679175450,0,true,163401300352,163401300416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923344080102,0,false,-191996100224,-191996100160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590178573,0,true,78547968,78548032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433076979,0,false,-78553664,-78553600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601461149,0,true,89829696,89829760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421794403,0,false,-89837056,-89836992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620436,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622165,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275631398458,0,true,163360120448,163360120512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923391857094,0,false,-191939209216,-191939209152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275756325348,0,true,163467794048,163467794112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923266930204,0,false,-192087973632,-192087973568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071260727433,0,false,-28620179584,-28620179520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071300763206,0,false,-28579088768,-28579088704⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (999/1000), zu := (7993/8000),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163284181184,163284181248⟩ : DyadicInterval 40),(⟨-191834310592,-191834310528⟩ : DyadicInterval 40),(⟨747971235769,747971255098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163401300352,163401300416⟩ : DyadicInterval 40),(⟨-191996100224,-191996100160⟩ : DyadicInterval 40),(⟨747949284447,747949303777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78550797,89833373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78547968,78548032⟩ : DyadicInterval 40),(⟨-78553664,-78553600⟩ : DyadicInterval 40),(⟨762123380788,762123400117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89829696,89829760⟩ : DyadicInterval 40),(⟨-89837056,-89836992⟩ : DyadicInterval 40),(⟨762123379892,762123399221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176119770682,176244697572⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163360120448,163360120512⟩ : DyadicInterval 40),(⟨-191939209216,-191939209152⟩ : DyadicInterval 40),(⟨747957004922,747957024252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163467794048,163467794112⟩ : DyadicInterval 40),(⟨-192087973632,-192087973568⟩ : DyadicInterval 40),(⟨747936813025,747936832355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28620179584,-28579088704⟩ : DyadicInterval 40),(⟨776412927968,776433492672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2301_ok : ecellOkT e2301 = true := by decide +kernel
theorem e2301_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2301 e2301_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '7993/8000', '3997/4000']  interval_lower 109120641/549755813888
noncomputable def e2302 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275451473160,0,true,163205025536,163205025600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923571782392,0,false,-191724987392,-191724987328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275587350291,0,true,163322153088,163322153152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923435905261,0,false,-191886760960,-191886760896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578911958,0,true,67282112,67282176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444343594,0,false,-67286272,-67286208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590179464,0,true,78548864,78548928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433076088,0,false,-78554496,-78554432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622164,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623659,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275528510259,0,true,163271433920,163271433984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923494745293,0,false,-191816703808,-191816703744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275653437173,0,true,163379116224,163379116288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923369818379,0,false,-191965451712,-191965451648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071293702440,0,false,-28586335488,-28586335424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071333714841,0,false,-28545269888,-28545269824⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163205025536,163205025600⟩ : DyadicInterval 40),(⟨-191724987392,-191724987328⟩ : DyadicInterval 40),(⟨747986060613,747986079942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163322153088,163322153152⟩ : DyadicInterval 40),(⟨-191886760960,-191886760896⟩ : DyadicInterval 40),(⟨747964120975,747964140304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67284182,78551688⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67282112,67282176⟩ : DyadicInterval 40),(⟨-67286272,-67286208⟩ : DyadicInterval 40),(⟨762123381514,762123400843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78548864,78548928⟩ : DyadicInterval 40),(⟨-78554496,-78554432⟩ : DyadicInterval 40),(⟨762123380755,762123400085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176016882483,176141809397⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163271433920,163271433984⟩ : DyadicInterval 40),(⟨-191816703808,-191816703744⟩ : DyadicInterval 40),(⟨747973623756,747973643086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163379116224,163379116288⟩ : DyadicInterval 40),(⟨-191965451712,-191965451648⟩ : DyadicInterval 40),(⟨747953443869,747953463199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28586335488,-28545269824⟩ : DyadicInterval 40),(⟨776396018528,776416570624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2302_ok : ecellOkT e2302 = true := by decide +kernel
theorem e2302_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2302 e2302_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '7993/8000', '3997/4000']  interval_lower 219438869/1099511627776
noncomputable def e2303 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275565324304,0,true,163303167296,163303167360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923457931248,0,false,-191860535488,-191860535424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275701215679,0,true,163420296704,163420296768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923322039873,0,false,-192022345920,-192022345856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578957155,0,true,67327296,67327360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444298397,0,false,-67331456,-67331392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590232197,0,true,78601600,78601664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433023355,0,false,-78607232,-78607168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622156,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623654,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275642411255,0,true,163369612736,163369612800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923380844297,0,false,-191952322560,-191952322496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275767345293,0,true,163477291520,163477291584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923255910259,0,false,-192101097280,-192101097216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071257194468,0,false,-28623805696,-28623805632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071297235036,0,false,-28582709824,-28582709760⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163303167296,163303167360⟩ : DyadicInterval 40),(⟨-191860535488,-191860535424⟩ : DyadicInterval 40),(⟨747967678611,747967697941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163420296704,163420296768⟩ : DyadicInterval 40),(⟨-192022345920,-192022345856⟩ : DyadicInterval 40),(⟨747945722193,747945741523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67329379,78604421⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67327296,67327360⟩ : DyadicInterval 40),(⟨-67331456,-67331392⟩ : DyadicInterval 40),(⟨762123381508,762123400838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78601600,78601664⟩ : DyadicInterval 40),(⟨-78607232,-78607168⟩ : DyadicInterval 40),(⟨762123380748,762123400077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176130783479,176255717517⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163369612736,163369612800⟩ : DyadicInterval 40),(⟨-191952322560,-191952322496⟩ : DyadicInterval 40),(⟨747955225499,747955244828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163477291520,163477291584⟩ : DyadicInterval 40),(⟨-192101097280,-192101097216⟩ : DyadicInterval 40),(⟨747935031196,747935050526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28623805696,-28582709760⟩ : DyadicInterval 40),(⟨776414738496,776435305728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2303_ok : ecellOkT e2303 = true := by decide +kernel
theorem e2303_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2303 e2303_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '3997/4000', '1599/1600']  interval_lower 107842221/549755813888
noncomputable def e2304 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275245754125,0,true,163027669760,163027669824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923777501427,0,false,-191480106304,-191480106240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275381617012,0,true,163144803904,163144803968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923641638540,0,false,-191641826816,-191641826752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567622700,0,true,55993472,55993536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455632852,0,false,-55996352,-55996288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578867601,0,true,67237760,67237824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444387951,0,false,-67241920,-67241856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623663,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624925,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275311699727,0,true,163084526272,163084526336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923711555825,0,false,-191558599808,-191558599744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275436619541,0,true,163192220800,163192220864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923586636011,0,false,-191707304320,-191707304256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071363128073,0,false,-28515083456,-28515083392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071403088933,0,false,-28474073472,-28474073408⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163027669760,163027669824⟩ : DyadicInterval 40),(⟨-191480106304,-191480106240⟩ : DyadicInterval 40),(⟨748019244628,748019263957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163144803904,163144803968⟩ : DyadicInterval 40),(⟨-191641826816,-191641826752⟩ : DyadicInterval 40),(⟨747997333361,747997352691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55994924,67239825⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55993472,55993536⟩ : DyadicInterval 40),(⟨-55996352,-55996288⟩ : DyadicInterval 40),(⟨762123382140,762123401469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67237760,67237824⟩ : DyadicInterval 40),(⟨-67241920,-67241856⟩ : DyadicInterval 40),(⟨762123381519,762123400849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175800071951,175924991765⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163084526272,163084526336⟩ : DyadicInterval 40),(⟨-191558599808,-191558599744⟩ : DyadicInterval 40),(⟨748008611431,748008630761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163192220800,163192220864⟩ : DyadicInterval 40),(⟨-191707304320,-191707304256⟩ : DyadicInterval 40),(⟨747988457939,747988477268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28515083456,-28474073408⟩ : DyadicInterval 40),(⟨776360420320,776380944608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2304_ok : ecellOkT e2304 = true := by decide +kernel
theorem e2304_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2304 e2304_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '3997/4000', '1599/1600']  interval_lower 216875849/1099511627776
noncomputable def e2305 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275359619513,0,true,163125839616,163125839680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923663636039,0,false,-191615641088,-191615641024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275495496644,0,true,163242975616,163242975680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923527758908,0,false,-191777398592,-191777398528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567660357,0,true,56031104,56031168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455595195,0,false,-56034048,-56033984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578912794,0,true,67282944,67283008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444342758,0,false,-67287104,-67287040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623658,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624921,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275425607846,0,true,163182727936,163182728000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923597647706,0,false,-191694195200,-191694195136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275550534781,0,true,163290418944,163290419008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923472720771,0,false,-191842926528,-191842926464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071326662745,0,false,-28552507520,-28552507456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071366651769,0,false,-28511467200,-28511467136⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163125839616,163125839680⟩ : DyadicInterval 40),(⟨-191615641088,-191615641024⟩ : DyadicInterval 40),(⟨748000882164,748000901494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163242975616,163242975680⟩ : DyadicInterval 40),(⟨-191777398592,-191777398528⟩ : DyadicInterval 40),(⟨747978954179,747978973509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56032581,67285018⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56031104,56031168⟩ : DyadicInterval 40),(⟨-56034048,-56033984⟩ : DyadicInterval 40),(⟨762123382168,762123401497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67282944,67283008⟩ : DyadicInterval 40),(⟨-67287104,-67287040⟩ : DyadicInterval 40),(⟨762123381514,762123400843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175913980070,176038907005⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163182727936,163182728000⟩ : DyadicInterval 40),(⟨-191694195200,-191694195136⟩ : DyadicInterval 40),(⟨747990235062,747990254391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163290418944,163290419008⟩ : DyadicInterval 40),(⟨-191842926528,-191842926464⟩ : DyadicInterval 40),(⟨747970067160,747970086489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28552507520,-28511467136⟩ : DyadicInterval 40),(⟨776379117184,776399656640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2305_ok : ecellOkT e2305 = true := by decide +kernel
theorem e2305_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2305 e2305_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '1599/1600', '1999/2000']  interval_lower 107757059/549755813888
noncomputable def e2306 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275267737378,0,true,163046623424,163046623488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923755518174,0,false,-191506271808,-191506271744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275403614509,0,true,163163767872,163163767936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923619641043,0,false,-191668013184,-191668013120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556423770,0,true,44795072,44795136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466831782,0,false,-44796928,-44796864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567661140,0,true,56031936,56032000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455594412,0,false,-56034816,-56034752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624920,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625951,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275322691211,0,true,163094002560,163094002624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923700564341,0,false,-191571683264,-191571683200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275447618172,0,true,163201702336,163201702400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923575637380,0,false,-191720398016,-191720397952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071359608338,0,false,-28518695680,-28518695616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071399573983,0,false,-28477680640,-28477680576⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163046623424,163046623488⟩ : DyadicInterval 40),(⟨-191506271808,-191506271744⟩ : DyadicInterval 40),(⟨748015700463,748015719792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163163767872,163163767936⟩ : DyadicInterval 40),(⟨-191668013184,-191668013120⟩ : DyadicInterval 40),(⟨747993784109,747993803439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44795994,56033364⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44795072,44795136⟩ : DyadicInterval 40),(⟨-44796928,-44796864⟩ : DyadicInterval 40),(⟨762123382654,762123401983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56031936,56032000⟩ : DyadicInterval 40),(⟨-56034816,-56034752⟩ : DyadicInterval 40),(⟨762123382136,762123401465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175811063435,175935990396⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163094002560,163094002624⟩ : DyadicInterval 40),(⟨-191571683264,-191571683200⟩ : DyadicInterval 40),(⟨748006838743,748006858072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163201702336,163201702400⟩ : DyadicInterval 40),(⟨-191720398016,-191720397952⟩ : DyadicInterval 40),(⟨747986682790,747986702120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28518695680,-28477680576⟩ : DyadicInterval 40),(⟨776362223904,776382750720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2306_ok : ecellOkT e2306 = true := by decide +kernel
theorem e2306_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2306 e2306_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '1599/1600', '1999/2000']  interval_lower 54176343/274877906944
noncomputable def e2307 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275381617010,0,true,163144803904,163144803968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923641638542,0,false,-191641826816,-191641826752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275517508385,0,true,163261950208,163261950272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923505747167,0,false,-191803605120,-191803605056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556453897,0,true,44825152,44825216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466801655,0,false,-44827072,-44827008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567698801,0,true,56069568,56069632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455556751,0,false,-56072512,-56072448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624916,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625949,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275436606453,0,true,163192209536,163192209600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923586649099,0,false,-191707288704,-191707288640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275561540538,0,true,163299905792,163299905856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923461715014,0,false,-191856030336,-191856030272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071323138449,0,false,-28556124544,-28556124480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071363132262,0,false,-28515079168,-28515079104⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163144803904,163144803968⟩ : DyadicInterval 40),(⟨-191641826816,-191641826752⟩ : DyadicInterval 40),(⟨747997333361,747997352691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163261950208,163261950272⟩ : DyadicInterval 40),(⟨-191803605120,-191803605056⟩ : DyadicInterval 40),(⟨747975400255,747975419584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44826121,56071025⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44825152,44825216⟩ : DyadicInterval 40),(⟨-44827072,-44827008⟩ : DyadicInterval 40),(⟨762123382684,762123402013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56069568,56069632⟩ : DyadicInterval 40),(⟨-56072512,-56072448⟩ : DyadicInterval 40),(⟨762123382164,762123401493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175924978677,176049912762⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163192209536,163192209600⟩ : DyadicInterval 40),(⟨-191707288704,-191707288640⟩ : DyadicInterval 40),(⟨747988460026,747988479355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163299905792,163299905856⟩ : DyadicInterval 40),(⟨-191856030336,-191856030272⟩ : DyadicInterval 40),(⟨747968289687,747968309016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28556124544,-28515079104⟩ : DyadicInterval 40),(⟨776380923168,776401465152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2307_ok : ecellOkT e2307 = true := by decide +kernel
theorem e2307_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2307 e2307_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '3997/4000', '1599/1600']  interval_lower 109035121/549755813888
noncomputable def e2308 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275473484901,0,true,163224000768,163224000832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923549770651,0,false,-191751192640,-191751192576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275609376276,0,true,163341138560,163341138624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923413879276,0,false,-191912987008,-191912986944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567698019,0,true,56068800,56068864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455557533,0,false,-56071680,-56071616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578957991,0,true,67328128,67328192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444297561,0,false,-67332288,-67332224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623652,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624917,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275539515966,0,true,163280920832,163280920896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923483739586,0,false,-191829807296,-191829807232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275664450027,0,true,163388608384,163388608448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923358805525,0,false,-191978565440,-191978565376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071290173811,0,false,-28589957056,-28589956992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071330191002,0,false,-28548886464,-28548886400⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163224000768,163224000832⟩ : DyadicInterval 40),(⟨-191751192640,-191751192576⟩ : DyadicInterval 40),(⟨747982507589,747982526919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163341138560,163341138624⟩ : DyadicInterval 40),(⟨-191912987008,-191912986944⟩ : DyadicInterval 40),(⟨747960562861,747960582191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56070243,67330215⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56068800,56068864⟩ : DyadicInterval 40),(⟨-56071680,-56071616⟩ : DyadicInterval 40),(⟨762123382132,762123401461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67328128,67328192⟩ : DyadicInterval 40),(⟨-67332288,-67332224⟩ : DyadicInterval 40),(⟨762123381508,762123400838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176027888190,176152822251⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163280920832,163280920896⟩ : DyadicInterval 40),(⟨-191829807296,-191829807232⟩ : DyadicInterval 40),(⟨747971846572,747971865902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163388608384,163388608448⟩ : DyadicInterval 40),(⟨-191978565440,-191978565376⟩ : DyadicInterval 40),(⟨747951664218,747951683548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28589957056,-28548886400⟩ : DyadicInterval 40),(⟨776397826816,776418381408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2308_ok : ecellOkT e2308 = true := by decide +kernel
theorem e2308_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2308 e2308_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '3997/4000', '1599/1600']  interval_lower 219267549/1099511627776
noncomputable def e2309 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275587350289,0,true,163322153088,163322153152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923435905263,0,false,-191886760960,-191886760896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275723255907,0,true,163439292736,163439292800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923299999645,0,false,-192048592192,-192048592128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567735681,0,true,56106432,56106496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455519871,0,false,-56109376,-56109312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579003191,0,true,67373312,67373376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444252361,0,false,-67377536,-67377472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623647,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624913,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275653424080,0,true,163379104896,163379104960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923369831472,0,false,-191965436096,-191965436032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275778365265,0,true,163486788992,163486789056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923244890287,0,false,-192114221120,-192114221056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071253661275,0,false,-28627432064,-28627432000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071293706636,0,false,-28586331200,-28586331136⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163322153088,163322153152⟩ : DyadicInterval 40),(⟨-191886760960,-191886760896⟩ : DyadicInterval 40),(⟨747964120975,747964140305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163439292736,163439292800⟩ : DyadicInterval 40),(⟨-192048592192,-192048592128⟩ : DyadicInterval 40),(⟨747942159460,747942178789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56107905,67375415⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56106432,56106496⟩ : DyadicInterval 40),(⟨-56109376,-56109312⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67373312,67373376⟩ : DyadicInterval 40),(⟨-67377536,-67377472⟩ : DyadicInterval 40),(⟨762123381535,762123400864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176141796304,176266737489⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163379104896,163379104960⟩ : DyadicInterval 40),(⟨-191965436096,-191965436032⟩ : DyadicInterval 40),(⟨747953445999,747953465328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163486788992,163486789056⟩ : DyadicInterval 40),(⟨-192114221120,-192114221056⟩ : DyadicInterval 40),(⟨747933249216,747933268546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28627432064,-28586331136⟩ : DyadicInterval 40),(⟨776416549184,776437118912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2309_ok : ecellOkT e2309 = true := by decide +kernel
theorem e2309_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2309 e2309_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '1599/1600', '1999/2000']  interval_lower 217899221/1099511627776
noncomputable def e2310 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275495496642,0,true,163242975616,163242975680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923527758910,0,false,-191777398592,-191777398528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275631402260,0,true,163360123712,163360123776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923391853292,0,false,-191939213760,-191939213696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556484025,0,true,44855296,44855360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466771527,0,false,-44857216,-44857152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567736465,0,true,56107200,56107264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455519087,0,false,-56110144,-56110080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624912,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625947,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275550521690,0,true,163290407680,163290407744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923472733862,0,false,-191842910912,-191842910848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275675462903,0,true,163398100480,163398100544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923347792649,0,false,-191991679360,-191991679296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071286644953,0,false,-28593578880,-28593578816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071326666938,0,false,-28552503232,-28552503168⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163242975616,163242975680⟩ : DyadicInterval 40),(⟨-191777398592,-191777398528⟩ : DyadicInterval 40),(⟨747978954179,747978973509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163360123712,163360123776⟩ : DyadicInterval 40),(⟨-191939213760,-191939213696⟩ : DyadicInterval 40),(⟨747957004323,747957023652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44856249,56108689⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44855296,44855360⟩ : DyadicInterval 40),(⟨-44857216,-44857152⟩ : DyadicInterval 40),(⟨762123382681,762123402011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56107200,56107264⟩ : DyadicInterval 40),(⟨-56110144,-56110080⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176038893914,176163835127⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163290407680,163290407744⟩ : DyadicInterval 40),(⟨-191842910912,-191842910848⟩ : DyadicInterval 40),(⟨747970069250,747970088580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163398100480,163398100544⟩ : DyadicInterval 40),(⟨-191991679360,-191991679296⟩ : DyadicInterval 40),(⟨747949884456,747949903785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28593578880,-28552503168⟩ : DyadicInterval 40),(⟨776399635200,776420192320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2310_ok : ecellOkT e2310 = true := by decide +kernel
theorem e2310_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2310 e2310_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '1599/1600', '1999/2000']  interval_lower 109547945/549755813888
noncomputable def e2311 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275609376273,0,true,163341138560,163341138624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923413879279,0,false,-191912987008,-191912986944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275745296136,0,true,163458288448,163458288512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923277959416,0,false,-192074839104,-192074839040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556514156,0,true,44885440,44885504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466741396,0,false,-44887360,-44887296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567774132,0,true,56144896,56144960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455481420,0,false,-56147840,-56147776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624908,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625944,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275664436933,0,true,163388597056,163388597120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923358818619,0,false,-191978549888,-191978549824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275789385263,0,true,163496286400,163496286464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923233870289,0,false,-192127345152,-192127345088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071250127852,0,false,-28631058752,-28631058688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071290178007,0,false,-28589952768,-28589952704⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163341138560,163341138624⟩ : DyadicInterval 40),(⟨-191912987008,-191912986944⟩ : DyadicInterval 40),(⟨747960562861,747960582191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163458288448,163458288512⟩ : DyadicInterval 40),(⟨-192074839104,-192074839040⟩ : DyadicInterval 40),(⟨747938596273,747938615603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44886380,56146356⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44885440,44885504⟩ : DyadicInterval 40),(⟨-44887360,-44887296⟩ : DyadicInterval 40),(⟨762123382679,762123402008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56144896,56144960⟩ : DyadicInterval 40),(⟨-56147840,-56147776⟩ : DyadicInterval 40),(⟨762123382156,762123401485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176152809157,176277757487⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163388597056,163388597120⟩ : DyadicInterval 40),(⟨-191978549888,-191978549824⟩ : DyadicInterval 40),(⟨747951666376,747951685705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163496286400,163496286464⟩ : DyadicInterval 40),(⟨-192127345152,-192127345088⟩ : DyadicInterval 40),(⟨747931467123,747931486453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28631058752,-28589952704⟩ : DyadicInterval 40),(⟨776418359968,776438932256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2311_ok : ecellOkT e2311 = true := by decide +kernel
theorem e2311_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2311 e2311_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '999/1000', '7993/8000']  interval_lower 110405571/549755813888
noncomputable def e2312 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275657135219,0,true,163382303616,163382303680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923366120333,0,false,-191969855232,-191969855168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275793026594,0,true,163499424576,163499424640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923230228958,0,false,-192131681728,-192131681664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590231306,0,true,78600704,78600768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433024246,0,false,-78606400,-78606336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601521420,0,true,89889920,89889984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421734132,0,false,-89897344,-89897280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620426,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622157,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275745292328,0,true,163458285184,163458285248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923277963224,0,false,-192074834560,-192074834496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275870226346,0,true,163565955328,163565955392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923153029206,0,false,-192223625856,-192223625792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071224200427,0,false,-28657670464,-28657670400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071264264368,0,false,-28616549376,-28616549312⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163382303616,163382303680⟩ : DyadicInterval 40),(⟨-191969855232,-191969855168⟩ : DyadicInterval 40),(⟨747952846313,747952865643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163499424576,163499424640⟩ : DyadicInterval 40),(⟨-192131681728,-192131681664⟩ : DyadicInterval 40),(⟨747930878249,747930897578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78603530,89893644⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78600704,78600768⟩ : DyadicInterval 40),(⟨-78606400,-78606336⟩ : DyadicInterval 40),(⟨762123380780,762123400109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89889920,89889984⟩ : DyadicInterval 40),(⟨-89897344,-89897280⟩ : DyadicInterval 40),(⟨762123379914,762123399243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176233664552,176358598570⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163458285184,163458285248⟩ : DyadicInterval 40),(⟨-192074834560,-192074834496⟩ : DyadicInterval 40),(⟨747938596875,747938616205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163565955328,163565955392⟩ : DyadicInterval 40),(⟨-192223625856,-192223625792⟩ : DyadicInterval 40),(⟨747918390551,747918409880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28657670464,-28616549312⟩ : DyadicInterval 40),(⟨776431658272,776452238112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2312_ok : ecellOkT e2312 = true := by decide +kernel
theorem e2312_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2312 e2312_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '999/1000', '7993/8000']  interval_lower 111007251/549755813888
noncomputable def e2313 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275770972119,0,true,163480417280,163480417344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923252283433,0,false,-192105416512,-192105416448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275906877738,0,true,163597540096,163597540160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923116377814,0,false,-192267279936,-192267279872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590284042,0,true,78653440,78653504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432971510,0,false,-78659136,-78659072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601581694,0,true,89950208,89950272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421673858,0,false,-89957632,-89957568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620416,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622150,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275859186203,0,true,163556441152,163556441216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923164069349,0,false,-192210476672,-192210476608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275984127349,0,true,163664107840,163664107904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923039128203,0,false,-192359294784,-192359294720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071187649821,0,false,-28695186944,-28695186880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071227741933,0,false,-28654035456,-28654035392⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163480417280,163480417344⟩ : DyadicInterval 40),(⟨-192105416512,-192105416448⟩ : DyadicInterval 40),(⟨747934444738,747934464068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163597540096,163597540160⟩ : DyadicInterval 40),(⟨-192267279936,-192267279872⟩ : DyadicInterval 40),(⟨747912459913,747912479243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78656266,89953918⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78653440,78653504⟩ : DyadicInterval 40),(⟨-78659136,-78659072⟩ : DyadicInterval 40),(⟨762123380772,762123400102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89950208,89950272⟩ : DyadicInterval 40),(⟨-89957632,-89957568⟩ : DyadicInterval 40),(⟨762123379904,762123399233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176347558427,176472499573⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163556441152,163556441216⟩ : DyadicInterval 40),(⟨-192210476672,-192210476608⟩ : DyadicInterval 40),(⟨747920176736,747920196065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163664107840,163664107904⟩ : DyadicInterval 40),(⟨-192359294784,-192359294720⟩ : DyadicInterval 40),(⟨747899955953,747899975283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28695186944,-28654035392⟩ : DyadicInterval 40),(⟨776450401312,776470996352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2313_ok : ecellOkT e2313 = true := by decide +kernel
theorem e2313_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2313 e2313_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '7993/8000', '3997/4000']  interval_lower 13789963/68719476736
noncomputable def e2314 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275679175448,0,true,163401300352,163401300416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923344080104,0,false,-191996100224,-191996100160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275815081067,0,true,163518431552,163518431616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923208174485,0,false,-192157947584,-192157947520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579002353,0,true,67372480,67372544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444253199,0,false,-67376704,-67376640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590284934,0,true,78654336,78654400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432970618,0,false,-78660032,-78659968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622149,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623648,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275756312253,0,true,163467782784,163467782848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923266943299,0,false,-192087958016,-192087957952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275881253416,0,true,163575458112,163575458176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923142002136,0,false,-192236759616,-192236759552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071220662894,0,false,-28661301440,-28661301376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071260731632,0,false,-28620175232,-28620175168⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163401300352,163401300416⟩ : DyadicInterval 40),(⟨-191996100224,-191996100160⟩ : DyadicInterval 40),(⟨747949284448,747949303777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163518431552,163518431616⟩ : DyadicInterval 40),(⟨-192157947584,-192157947520⟩ : DyadicInterval 40),(⟨747927311306,747927330635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67374577,78657158⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67372480,67372544⟩ : DyadicInterval 40),(⟨-67376704,-67376640⟩ : DyadicInterval 40),(⟨762123381535,762123400864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78654336,78654400⟩ : DyadicInterval 40),(⟨-78660032,-78659968⟩ : DyadicInterval 40),(⟨762123380772,762123400102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176244684477,176369625640⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163467782784,163467782848⟩ : DyadicInterval 40),(⟨-192087958016,-192087957952⟩ : DyadicInterval 40),(⟨747936815121,747936834450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163575458112,163575458176⟩ : DyadicInterval 40),(⟨-192236759616,-192236759552⟩ : DyadicInterval 40),(⟨747916606388,747916625718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28661301440,-28620175168⟩ : DyadicInterval 40),(⟨776433471200,776454053600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2314_ok : ecellOkT e2314 = true := by decide +kernel
theorem e2314_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2314 e2314_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '7993/8000', '3997/4000']  interval_lower 221842589/1099511627776
noncomputable def e2315 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275793026592,0,true,163499424576,163499424640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923230228960,0,false,-192131681728,-192131681664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275928946454,0,true,163616557632,163616557696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923094309098,0,false,-192293566016,-192293565952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579047557,0,true,67417664,67417728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444207995,0,false,-67421888,-67421824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590337675,0,true,78707072,78707136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432917877,0,false,-78712768,-78712704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622141,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623642,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275870213248,0,true,163565944064,163565944128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923153042304,0,false,-192223610240,-192223610176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275995161539,0,true,163673615936,163673616000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923028094013,0,false,-192372438656,-192372438592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071184107718,0,false,-28698822656,-28698822592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071224204630,0,false,-28657666176,-28657666112⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163499424576,163499424640⟩ : DyadicInterval 40),(⟨-192131681728,-192131681664⟩ : DyadicInterval 40),(⟨747930878249,747930897579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163616557632,163616557696⟩ : DyadicInterval 40),(⟨-192293566016,-192293565952⟩ : DyadicInterval 40),(⟨747908888340,747908907669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67419781,78709899⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67417664,67417728⟩ : DyadicInterval 40),(⟨-67421888,-67421824⟩ : DyadicInterval 40),(⟨762123381529,762123400859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78707072,78707136⟩ : DyadicInterval 40),(⟨-78712768,-78712704⟩ : DyadicInterval 40),(⟨762123380765,762123400094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176358585472,176483533763⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163565944064,163565944128⟩ : DyadicInterval 40),(⟨-192223610240,-192223610176⟩ : DyadicInterval 40),(⟨747918392650,747918411979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163673615936,163673616000⟩ : DyadicInterval 40),(⟨-192372438656,-192372438592⟩ : DyadicInterval 40),(⟨747898169455,747898188785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28698822656,-28657666112⟩ : DyadicInterval 40),(⟨776452216672,776472814208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2315_ok : ecellOkT e2315 = true := by decide +kernel
theorem e2315_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2315 e2315_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '999/1000', '7993/8000']  interval_lower 223221323/1099511627776
noncomputable def e2316 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275884809019,0,true,163578522240,163578522304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923138446533,0,false,-192240994496,-192240994432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276020728882,0,true,163695646848,163695646912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923002526670,0,false,-192402894912,-192402894848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590336783,0,true,78706176,78706240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432918769,0,false,-78711872,-78711808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601641973,0,true,90010496,90010560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421613579,0,false,-90017920,-90017856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620406,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622142,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275973080085,0,true,163654588416,163654588480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923050175467,0,false,-192346135552,-192346135488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276098028343,0,true,163762251584,163762251648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922925227209,0,false,-192494980480,-192494980416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071151075620,0,false,-28732728832,-28732728768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071191195901,0,false,-28691547072,-28691547008⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163578522240,163578522304⟩ : DyadicInterval 40),(⟨-192240994496,-192240994432⟩ : DyadicInterval 40),(⟨747916031032,747916050362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163695646848,163695646912⟩ : DyadicInterval 40),(⟨-192402894912,-192402894848⟩ : DyadicInterval 40),(⟨747894029503,747894048833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78709007,90014197⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78706176,78706240⟩ : DyadicInterval 40),(⟨-78711872,-78711808⟩ : DyadicInterval 40),(⟨762123380765,762123400094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90010496,90010560⟩ : DyadicInterval 40),(⟨-90017920,-90017856⟩ : DyadicInterval 40),(⟨762123379894,762123399224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176461452309,176586400567⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163654588416,163654588480⟩ : DyadicInterval 40),(⟨-192346135552,-192346135488⟩ : DyadicInterval 40),(⟨747901744466,747901763796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163762251584,163762251648⟩ : DyadicInterval 40),(⟨-192494980480,-192494980416⟩ : DyadicInterval 40),(⟨747881509261,747881528590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28732728832,-28691547008⟩ : DyadicInterval 40),(⟨776469157120,776489767296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2316_ok : ecellOkT e2316 = true := by decide +kernel
theorem e2316_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2316 e2316_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '999/1000', '7993/8000']  interval_lower 224430897/1099511627776
noncomputable def e2317 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275998645920,0,true,163676618368,163676618432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923024609632,0,false,-192376589248,-192376589184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276134580026,0,true,163793744832,163793744896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922888675526,0,false,-192538526592,-192538526528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590389526,0,true,78758912,78758976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432866026,0,false,-78764608,-78764544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601702257,0,true,90070784,90070848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421553295,0,false,-90078208,-90078144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620396,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622135,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276086973952,0,true,163752726912,163752726976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922936281600,0,false,-192481811072,-192481811008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276211929344,0,true,163860386624,163860386688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922811326208,0,false,-192630682944,-192630682880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071114477818,0,false,-28770296256,-28770296192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071154626277,0,false,-28729084160,-28729084096⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163676618368,163676618432⟩ : DyadicInterval 40),(⟨-192376589248,-192376589184⟩ : DyadicInterval 40),(⟨747897605295,747897624625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163793744832,163793744896⟩ : DyadicInterval 40),(⟨-192538526592,-192538526528⟩ : DyadicInterval 40),(⟨747875586990,747875606320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78761750,90074481⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78758912,78758976⟩ : DyadicInterval 40),(⟨-78764608,-78764544⟩ : DyadicInterval 40),(⟨762123380757,762123400087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90070784,90070848⟩ : DyadicInterval 40),(⟨-90078208,-90078144⟩ : DyadicInterval 40),(⟨762123379884,762123399214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176575346176,176700301568⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163752726912,163752726976⟩ : DyadicInterval 40),(⟨-192481811072,-192481811008⟩ : DyadicInterval 40),(⟨747883300052,747883319382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163860386624,163860386688⟩ : DyadicInterval 40),(⟨-192630682944,-192630682880⟩ : DyadicInterval 40),(⟨747863050432,747863069762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28770296256,-28729084096⟩ : DyadicInterval 40),(⟨776487925664,776508551008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2317_ok : ecellOkT e2317 = true := by decide +kernel
theorem e2317_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2317 e2317_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '7993/8000', '3997/4000']  interval_lower 27881111/137438953472
noncomputable def e2318 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275906877736,0,true,163597540096,163597540160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923116377816,0,false,-192267279936,-192267279872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276042811842,0,true,163714674944,163714675008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922980443710,0,false,-192429201216,-192429201152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579092763,0,true,67462912,67462976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444162789,0,false,-67467072,-67467008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590390419,0,true,78759808,78759872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432865133,0,false,-78765504,-78765440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622133,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623637,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275984114249,0,true,163664096576,163664096640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923039141303,0,false,-192359279168,-192359279104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276109069653,0,true,163771764992,163771765056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922914185899,0,false,-192508134464,-192508134400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071147528943,0,false,-28736369408,-28736369344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071187654027,0,false,-28695182592,-28695182528⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163597540096,163597540160⟩ : DyadicInterval 40),(⟨-192267279936,-192267279872⟩ : DyadicInterval 40),(⟨747912459914,747912479243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163714674944,163714675008⟩ : DyadicInterval 40),(⟨-192429201216,-192429201152⟩ : DyadicInterval 40),(⟨747890453292,747890472622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67464987,78762643⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67462912,67462976⟩ : DyadicInterval 40),(⟨-67467072,-67467008⟩ : DyadicInterval 40),(⟨762123381492,762123400821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78759808,78759872⟩ : DyadicInterval 40),(⟨-78765504,-78765440⟩ : DyadicInterval 40),(⟨762123380757,762123400087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176472486473,176597441877⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163664096576,163664096640⟩ : DyadicInterval 40),(⟨-192359279168,-192359279104⟩ : DyadicInterval 40),(⟨747899958055,747899977385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163771764992,163771765056⟩ : DyadicInterval 40),(⟨-192508134464,-192508134400⟩ : DyadicInterval 40),(⟨747879720424,747879739753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28736369408,-28695182528⟩ : DyadicInterval 40),(⟨776470974880,776491587584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2318_ok : ecellOkT e2318 = true := by decide +kernel
theorem e2318_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2318 e2318_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '7993/8000', '3997/4000']  interval_lower 224257915/1099511627776
noncomputable def e2319 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276020728880,0,true,163695646848,163695646912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923002526672,0,false,-192402894912,-192402894848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276156677230,0,true,163812783488,163812783552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922866578322,0,false,-192564853056,-192564852992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579137972,0,true,67508096,67508160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444117580,0,false,-67512320,-67512256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590443168,0,true,78812544,78812608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432812384,0,false,-78818240,-78818176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622126,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623631,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276098015240,0,true,163762240320,163762240384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922925240312,0,false,-192494964864,-192494964800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276222977777,0,true,163869905280,163869905344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922800277775,0,false,-192643846976,-192643846912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071110926564,0,false,-28773941696,-28773941632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071151079830,0,false,-28732724544,-28732724480⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163695646848,163695646912⟩ : DyadicInterval 40),(⟨-192402894912,-192402894848⟩ : DyadicInterval 40),(⟨747894029503,747894048833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163812783488,163812783552⟩ : DyadicInterval 40),(⟨-192564853056,-192564852992⟩ : DyadicInterval 40),(⟨747872006109,747872025439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67510196,78815392⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67508096,67508160⟩ : DyadicInterval 40),(⟨-67512320,-67512256⟩ : DyadicInterval 40),(⟨762123381518,762123400847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78812544,78812608⟩ : DyadicInterval 40),(⟨-78818240,-78818176⟩ : DyadicInterval 40),(⟨762123380750,762123400079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176586387464,176711350001⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163762240320,163762240384⟩ : DyadicInterval 40),(⟨-192494964864,-192494964800⟩ : DyadicInterval 40),(⟨747881511366,747881530696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163869905280,163869905344⟩ : DyadicInterval 40),(⟨-192643846976,-192643846912⟩ : DyadicInterval 40),(⟨747861259263,747861278592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28773941696,-28732724480⟩ : DyadicInterval 40),(⟨776489745856,776510373728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2319_ok : ecellOkT e2319 = true := by decide +kernel
theorem e2319_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2319 e2319_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '3997/4000', '1599/1600']  interval_lower 3444805/17179869184
noncomputable def e2320 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275701215677,0,true,163420296704,163420296768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923322039875,0,false,-192022345920,-192022345856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275837135539,0,true,163537438144,163537438208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923186120013,0,false,-192184214080,-192184214016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567773348,0,true,56144128,56144192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455482204,0,false,-56147008,-56146944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579048394,0,true,67418496,67418560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444207158,0,false,-67422720,-67422656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623641,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624909,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275767332197,0,true,163477280256,163477280320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923255923355,0,false,-192101081664,-192101081600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275892280508,0,true,163584960896,163584960960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923130975044,0,false,-192249893568,-192249893504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071217125132,0,false,-28664932672,-28664932608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071257198668,0,false,-28623801408,-28623801344⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163420296704,163420296768⟩ : DyadicInterval 40),(⟨-192022345920,-192022345856⟩ : DyadicInterval 40),(⟨747945722193,747945741523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163537438144,163537438208⟩ : DyadicInterval 40),(⟨-192184214080,-192184214016⟩ : DyadicInterval 40),(⟨747923743947,747923763276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56145572,67420618⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56144128,56144192⟩ : DyadicInterval 40),(⟨-56147008,-56146944⟩ : DyadicInterval 40),(⟨762123382124,762123401454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67418496,67418560⟩ : DyadicInterval 40),(⟨-67422720,-67422656⟩ : DyadicInterval 40),(⟨762123381529,762123400858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176255704421,176380652732⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163477280256,163477280320⟩ : DyadicInterval 40),(⟨-192101081664,-192101081600⟩ : DyadicInterval 40),(⟨747935033292,747935052622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163584960896,163584960960⟩ : DyadicInterval 40),(⟨-192249893568,-192249893504⟩ : DyadicInterval 40),(⟨747914822075,747914841405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28664932672,-28623801344⟩ : DyadicInterval 40),(⟨776435284288,776455869216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2320_ok : ecellOkT e2320 = true := by decide +kernel
theorem e2320_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2320 e2320_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '3997/4000', '1599/1600']  interval_lower 221670333/1099511627776
noncomputable def e2321 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275815081064,0,true,163518431552,163518431616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923208174488,0,false,-192157947584,-192157947520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275951015171,0,true,163635574848,163635574912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923072240381,0,false,-192319852736,-192319852672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567811018,0,true,56181760,56181824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455444534,0,false,-56184704,-56184640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579093602,0,true,67463744,67463808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444161950,0,false,-67467904,-67467840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623636,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624906,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275881240318,0,true,163575446848,163575446912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923142015234,0,false,-192236744000,-192236743936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276006195756,0,true,163683123968,163683124032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923017059796,0,false,-192385582720,-192385582656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071180565384,0,false,-28702458688,-28702458624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071220667097,0,false,-28661297152,-28661297088⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163518431552,163518431616⟩ : DyadicInterval 40),(⟨-192157947584,-192157947520⟩ : DyadicInterval 40),(⟨747927311307,747927330636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163635574848,163635574912⟩ : DyadicInterval 40),(⟨-192319852736,-192319852672⟩ : DyadicInterval 40),(⟨747905316311,747905335640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56183242,67465826⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56181760,56181824⟩ : DyadicInterval 40),(⟨-56184704,-56184640⟩ : DyadicInterval 40),(⟨762123382153,762123401482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67463744,67463808⟩ : DyadicInterval 40),(⟨-67467904,-67467840⟩ : DyadicInterval 40),(⟨762123381492,762123400821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176369612542,176494567980⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163575446848,163575446912⟩ : DyadicInterval 40),(⟨-192236744000,-192236743936⟩ : DyadicInterval 40),(⟨747916608487,747916627817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163683123968,163683124032⟩ : DyadicInterval 40),(⟨-192385582720,-192385582656⟩ : DyadicInterval 40),(⟨747896382843,747896402172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28702458688,-28661297088⟩ : DyadicInterval 40),(⟨776454032160,776474632224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2321_ok : ecellOkT e2321 = true := by decide +kernel
theorem e2321_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2321 e2321_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '1599/1600', '1999/2000']  interval_lower 55073903/274877906944
noncomputable def e2322 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275723255905,0,true,163439292736,163439292800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923299999647,0,false,-192048592192,-192048592128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275859190012,0,true,163556444480,163556444544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923164065540,0,false,-192210481216,-192210481152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556544290,0,true,44915584,44915648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466711262,0,false,-44917440,-44917376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567811802,0,true,56182528,56182592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455443750,0,false,-56185472,-56185408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624905,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625942,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275778352169,0,true,163486777728,163486777792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923244903383,0,false,-192114205504,-192114205440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275903307631,0,true,163594463552,163594463616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923119947921,0,false,-192263027648,-192263027584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071213587140,0,false,-28668564096,-28668564032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071253665475,0,false,-28627427776,-28627427712⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163439292736,163439292800⟩ : DyadicInterval 40),(⟨-192048592192,-192048592128⟩ : DyadicInterval 40),(⟨747942159460,747942178789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163556444480,163556444544⟩ : DyadicInterval 40),(⟨-192210481216,-192210481152⟩ : DyadicInterval 40),(⟨747920176096,747920195426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44916514,56184026⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44915584,44915648⟩ : DyadicInterval 40),(⟨-44917440,-44917376⟩ : DyadicInterval 40),(⟨762123382645,762123401974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56182528,56182592⟩ : DyadicInterval 40),(⟨-56185472,-56185408⟩ : DyadicInterval 40),(⟨762123382152,762123401482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176266724393,176391679855⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163486777728,163486777792⟩ : DyadicInterval 40),(⟨-192114205504,-192114205440⟩ : DyadicInterval 40),(⟨747933251313,747933270642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163594463552,163594463616⟩ : DyadicInterval 40),(⟨-192263027648,-192263027584⟩ : DyadicInterval 40),(⟨747913037659,747913056989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28668564096,-28627427712⟩ : DyadicInterval 40),(⟨776437097472,776457684928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2322_ok : ecellOkT e2322 = true := by decide +kernel
theorem e2322_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2322 e2322_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '1599/1600', '1999/2000']  interval_lower 221497997/1099511627776
noncomputable def e2323 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275837135537,0,true,163537438144,163537438208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923186120015,0,false,-192184214080,-192184214016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275973083887,0,true,163654591680,163654591744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923050171665,0,false,-192346140032,-192346139968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556574424,0,true,44945728,44945792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466681128,0,false,-44947584,-44947520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567849474,0,true,56220224,56220288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455406078,0,false,-56223168,-56223104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624901,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625939,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275892267409,0,true,163584949568,163584949632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923130988143,0,false,-192249877952,-192249877888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276017229996,0,true,163692631936,163692632000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923006025556,0,false,-192398726912,-192398726848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071177022822,0,false,-28706094976,-28706094912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071217129336,0,false,-28664928320,-28664928256⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163537438144,163537438208⟩ : DyadicInterval 40),(⟨-192184214080,-192184214016⟩ : DyadicInterval 40),(⟨747923743947,747923763276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163654591680,163654591744⟩ : DyadicInterval 40),(⟨-192346140032,-192346139968⟩ : DyadicInterval 40),(⟨747901743837,747901763167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44946648,56221698⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44945728,44945792⟩ : DyadicInterval 40),(⟨-44947584,-44947520⟩ : DyadicInterval 40),(⟨762123382642,762123401971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56220224,56220288⟩ : DyadicInterval 40),(⟨-56223168,-56223104⟩ : DyadicInterval 40),(⟨762123382149,762123401478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176380639633,176505602220⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163584949568,163584949632⟩ : DyadicInterval 40),(⟨-192249877952,-192249877888⟩ : DyadicInterval 40),(⟨747914824213,747914843542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163692631936,163692632000⟩ : DyadicInterval 40),(⟨-192398726912,-192398726848⟩ : DyadicInterval 40),(⟨747894596091,747894615420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28706094976,-28664928256⟩ : DyadicInterval 40),(⟨776455847744,776476450368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2323_ok : ecellOkT e2323 = true := by decide +kernel
theorem e2323_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2323 e2323_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '3997/4000', '1599/1600']  interval_lower 222876377/1099511627776
noncomputable def e2324 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275928946452,0,true,163616557632,163616557696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923094309100,0,false,-192293566016,-192293565952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276064894802,0,true,163733702720,163733702784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922958360750,0,false,-192455508096,-192455508032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567848689,0,true,56219456,56219520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455406863,0,false,-56222400,-56222336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579138811,0,true,67508928,67508992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444116741,0,false,-67513152,-67513088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623630,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624902,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275995148438,0,true,163673604672,163673604736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923028107114,0,false,-192372423040,-192372422976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276120110992,0,true,163781278272,163781278336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922903144560,0,false,-192521288576,-192521288512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071143982035,0,false,-28740010240,-28740010176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071184111925,0,false,-28698818368,-28698818304⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163616557632,163616557696⟩ : DyadicInterval 40),(⟨-192293566016,-192293565952⟩ : DyadicInterval 40),(⟨747908888340,747908907669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163733702720,163733702784⟩ : DyadicInterval 40),(⟨-192455508096,-192455508032⟩ : DyadicInterval 40),(⟨747886876598,747886895928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56220913,67511035⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56219456,56219520⟩ : DyadicInterval 40),(⟨-56222400,-56222336⟩ : DyadicInterval 40),(⟨762123382149,762123401478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67508928,67508992⟩ : DyadicInterval 40),(⟨-67513152,-67513088⟩ : DyadicInterval 40),(⟨762123381518,762123400847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176483520662,176608483216⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163673604672,163673604736⟩ : DyadicInterval 40),(⟨-192372423040,-192372422976⟩ : DyadicInterval 40),(⟨747898171558,747898190887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163781278272,163781278336⟩ : DyadicInterval 40),(⟨-192521288576,-192521288512⟩ : DyadicInterval 40),(⟨747877931482,747877950812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28740010240,-28698818304⟩ : DyadicInterval 40),(⟨776472792768,776493408000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2324_ok : ecellOkT e2324 = true := by decide +kernel
theorem e2324_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2324 e2324_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '3997/4000', '1599/1600']  interval_lower 224085023/1099511627776
noncomputable def e2325 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276042811840,0,true,163714674944,163714675008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922980443712,0,false,-192429201216,-192429201152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276178774434,0,true,163831821888,163831821952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922844481118,0,false,-192591180224,-192591180160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567886365,0,true,56257088,56257152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455369187,0,false,-56260032,-56259968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579184025,0,true,67554112,67554176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444071527,0,false,-67558336,-67558272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623625,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624898,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276109056549,0,true,163771753728,163771753792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922914199003,0,false,-192508118848,-192508118784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276234026237,0,true,163879423872,163879423936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922789229315,0,false,-192657011264,-192657011200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071107375079,0,false,-28777587328,-28777587264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071147533154,0,false,-28736365120,-28736365056⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163714674944,163714675008⟩ : DyadicInterval 40),(⟨-192429201216,-192429201152⟩ : DyadicInterval 40),(⟨747890453293,747890472622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163831821888,163831821952⟩ : DyadicInterval 40),(⟨-192591180224,-192591180160⟩ : DyadicInterval 40),(⟨747868424760,747868444090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56258589,67556249⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56257088,56257152⟩ : DyadicInterval 40),(⟨-56260032,-56259968⟩ : DyadicInterval 40),(⟨762123382145,762123401474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67554112,67554176⟩ : DyadicInterval 40),(⟨-67558336,-67558272⟩ : DyadicInterval 40),(⟨762123381513,762123400842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176597428773,176722398461⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163771753728,163771753792⟩ : DyadicInterval 40),(⟨-192508118848,-192508118784⟩ : DyadicInterval 40),(⟨747879722529,747879741859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163879423872,163879423936⟩ : DyadicInterval 40),(⟨-192657011264,-192657011200⟩ : DyadicInterval 40),(⟨747859468006,747859487336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28777587328,-28736365056⟩ : DyadicInterval 40),(⟨776491566144,776512196544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2325_ok : ecellOkT e2325 = true := by decide +kernel
theorem e2325_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2325 e2325_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '1599/1600', '1999/2000']  interval_lower 13918979/68719476736
noncomputable def e2326 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275951015169,0,true,163635574848,163635574912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923072240383,0,false,-192319852736,-192319852672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276086977763,0,true,163752730176,163752730240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922936277789,0,false,-192481815616,-192481815552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556604563,0,true,44975808,44975872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466650989,0,false,-44977728,-44977664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567887149,0,true,56257920,56257984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455368403,0,false,-56260864,-56260800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624897,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625937,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276006182655,0,true,163683112704,163683112768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923017072897,0,false,-192385567104,-192385567040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276131152357,0,true,163790791552,163790791616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922892103195,0,false,-192534442944,-192534442880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071140434898,0,false,-28743651328,-28743651264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071180569591,0,false,-28702454400,-28702454336⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163635574848,163635574912⟩ : DyadicInterval 40),(⟨-192319852736,-192319852672⟩ : DyadicInterval 40),(⟨747905316311,747905335640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163752730176,163752730240⟩ : DyadicInterval 40),(⟨-192481815616,-192481815552⟩ : DyadicInterval 40),(⟨747883299448,747883318778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44976787,56259373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44975808,44975872⟩ : DyadicInterval 40),(⟨-44977728,-44977664⟩ : DyadicInterval 40),(⟨762123382672,762123402001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56257920,56257984⟩ : DyadicInterval 40),(⟨-56260864,-56260800⟩ : DyadicInterval 40),(⟨762123382145,762123401474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176494554879,176619524581⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163683112704,163683112768⟩ : DyadicInterval 40),(⟨-192385567104,-192385567040⟩ : DyadicInterval 40),(⟨747896384945,747896404275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163790791552,163790791616⟩ : DyadicInterval 40),(⟨-192534442944,-192534442880⟩ : DyadicInterval 40),(⟨747876142416,747876161746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28743651328,-28702454336⟩ : DyadicInterval 40),(⟨776474610784,776495228544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2326_ok : ecellOkT e2326 = true := by decide +kernel
theorem e2326_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2326 e2326_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '1599/1600', '1999/2000']  interval_lower 223911753/1099511627776
noncomputable def e2327 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276064894800,0,true,163733702720,163733702784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922958360752,0,false,-192455508096,-192455508032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276200871638,0,true,163850859904,163850859968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922822383914,0,false,-192617507968,-192617507904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556634703,0,true,45005952,45006016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466620849,0,false,-45007872,-45007808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567924828,0,true,56295552,56295616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455330724,0,false,-56298496,-56298432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624893,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625934,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276120097888,0,true,163781267008,163781267072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922903157664,0,false,-192521272960,-192521272896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276245074723,0,true,163888942400,163888942464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922778180829,0,false,-192670175680,-192670175616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071103823364,0,false,-28781233216,-28781233152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071143986246,0,false,-28740005952,-28740005888⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163733702720,163733702784⟩ : DyadicInterval 40),(⟨-192455508096,-192455508032⟩ : DyadicInterval 40),(⟨747886876599,747886895928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163850859904,163850859968⟩ : DyadicInterval 40),(⟨-192617507968,-192617507904⟩ : DyadicInterval 40),(⟨747864842964,747864862293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45006927,56297052⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45005952,45006016⟩ : DyadicInterval 40),(⟨-45007872,-45007808⟩ : DyadicInterval 40),(⟨762123382669,762123401998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56295552,56295616⟩ : DyadicInterval 40),(⟨-56298496,-56298432⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176608470112,176733446947⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163781267008,163781267072⟩ : DyadicInterval 40),(⟨-192521272960,-192521272896⟩ : DyadicInterval 40),(⟨747877933588,747877952918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163888942400,163888942464⟩ : DyadicInterval 40),(⟨-192670175680,-192670175616⟩ : DyadicInterval 40),(⟨747857676608,747857695937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28781233216,-28740005888⟩ : DyadicInterval 40),(⟨776493386560,776514019488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2327_ok : ecellOkT e2327 = true := by decide +kernel
theorem e2327_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2327 e2327_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '1999/2000', '7997/8000']  interval_lower 215343727/1099511627776
noncomputable def e2328 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275289720632,0,true,163065576832,163065576896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923733534920,0,false,-191532437952,-191532437888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275425612006,0,true,163182731520,163182731584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923597643546,0,false,-191694200128,-191694200064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545224786,0,true,33596480,33596544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478030766,0,false,-33597568,-33597504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556454625,0,true,44825920,44825984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466800927,0,false,-44827776,-44827712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625948,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626750,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275333682725,0,true,163103478784,163103478848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923689572827,0,false,-191584766912,-191584766848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275458616833,0,true,163211183744,163211183808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923564638719,0,false,-191733491968,-191733491904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071356088374,0,false,-28522308160,-28522308096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071396058804,0,false,-28481288064,-28481288000⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163065576832,163065576896⟩ : DyadicInterval 40),(⟨-191532437952,-191532437888⟩ : DyadicInterval 40),(⟨748012155813,748012175142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163182731520,163182731584⟩ : DyadicInterval 40),(⟨-191694200128,-191694200064⟩ : DyadicInterval 40),(⟨747990234382,747990253711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33597010,44826849⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33596480,33596544⟩ : DyadicInterval 40),(⟨-33597568,-33597504⟩ : DyadicInterval 40),(⟨762123383069,762123402398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44825920,44825984⟩ : DyadicInterval 40),(⟨-44827776,-44827712⟩ : DyadicInterval 40),(⟨762123382652,762123401981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175822054949,175946989057⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163103478784,163103478848⟩ : DyadicInterval 40),(⟨-191584766912,-191584766848⟩ : DyadicInterval 40),(⟨748005065941,748005085271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163211183744,163211183808⟩ : DyadicInterval 40),(⟨-191733491968,-191733491904⟩ : DyadicInterval 40),(⟨747984907593,747984926923⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28522308160,-28481288000⟩ : DyadicInterval 40),(⟨776364027616,776384556960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2328_ok : ecellOkT e2328 = true := by decide +kernel
theorem e2328_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2328 e2328_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '1999/2000', '7997/8000']  interval_lower 216534403/1099511627776
noncomputable def e2329 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275403614507,0,true,163163767872,163163767936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923619641045,0,false,-191668013184,-191668013120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275539520126,0,true,163280924416,163280924480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923483735426,0,false,-191829812224,-191829812160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545247381,0,true,33619072,33619136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478008171,0,false,-33620160,-33620096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556484753,0,true,44856000,44856064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466770799,0,false,-44857920,-44857856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625945,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626749,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275447605084,0,true,163201691008,163201691072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923575650468,0,false,-191720382464,-191720382400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275572546320,0,true,163309392512,163309392576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923450709232,0,false,-191869134336,-191869134272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071319613925,0,false,-28559741824,-28559741760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071359612528,0,false,-28518691392,-28518691328⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163163767872,163163767936⟩ : DyadicInterval 40),(⟨-191668013184,-191668013120⟩ : DyadicInterval 40),(⟨747993784110,747993803439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163280924416,163280924480⟩ : DyadicInterval 40),(⟨-191829812224,-191829812160⟩ : DyadicInterval 40),(⟨747971845891,747971865220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33619605,44856977⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33619072,33619136⟩ : DyadicInterval 40),(⟨-33620160,-33620096⟩ : DyadicInterval 40),(⟨762123383068,762123402397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44856000,44856064⟩ : DyadicInterval 40),(⟨-44857920,-44857856⟩ : DyadicInterval 40),(⟨762123382681,762123402011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175935977308,176060918544⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163201691008,163201691072⟩ : DyadicInterval 40),(⟨-191720382464,-191720382400⟩ : DyadicInterval 40),(⟨747986684942,747986704271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163309392512,163309392576⟩ : DyadicInterval 40),(⟨-191869134336,-191869134272⟩ : DyadicInterval 40),(⟨747966512139,747966531468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28559741824,-28518691328⟩ : DyadicInterval 40),(⟨776382729280,776403273792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2329_ok : ecellOkT e2329 = true := by decide +kernel
theorem e2329_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2329 e2329_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '7997/8000', '3999/4000']  interval_lower 215173311/1099511627776
noncomputable def e2330 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275311703885,0,true,163084529856,163084529920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923711551667,0,false,-191558604736,-191558604672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275447609503,0,true,163201694848,163201694912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923575646049,0,false,-191720387712,-191720387648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534025751,0,true,22397696,22397760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489229801,0,false,-22398208,-22398144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545248057,0,true,33619712,33619776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478007495,0,false,-33620800,-33620736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626747,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627320,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275344674261,0,true,163112954944,163112955008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923678581291,0,false,-191597850688,-191597850624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275469615518,0,true,163220665152,163220665216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923553640034,0,false,-191746586048,-191746585984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071352568182,0,false,-28525920896,-28525920832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071392543398,0,false,-28484895744,-28484895680⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163084529856,163084529920⟩ : DyadicInterval 40),(⟨-191558604736,-191558604672⟩ : DyadicInterval 40),(⟨748008610752,748008630082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163201694848,163201694912⟩ : DyadicInterval 40),(⟨-191720387712,-191720387648⟩ : DyadicInterval 40),(⟨747986684205,747986703535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22397975,33620281⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22397696,22397760⟩ : DyadicInterval 40),(⟨-22398208,-22398144⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33619712,33619776⟩ : DyadicInterval 40),(⟨-33620800,-33620736⟩ : DyadicInterval 40),(⟨762123383067,762123402396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175833046485,175957987742⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163112954944,163112955008⟩ : DyadicInterval 40),(⟨-191597850688,-191597850624⟩ : DyadicInterval 40),(⟨748003293002,748003312331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163220665152,163220665216⟩ : DyadicInterval 40),(⟨-191746586048,-191746585984⟩ : DyadicInterval 40),(⟨747983132220,747983151549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28525920896,-28484895680⟩ : DyadicInterval 40),(⟨776365831456,776386363328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2330_ok : ecellOkT e2330 = true := by decide +kernel
theorem e2330_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2330 e2330_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '7997/8000', '3999/4000']  interval_lower 108181855/549755813888
noncomputable def e2331 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275425612004,0,true,163182731520,163182731584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923597643548,0,false,-191694200128,-191694200064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275561531867,0,true,163299898304,163299898368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923461723685,0,false,-191856020032,-191856019968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534040814,0,true,22412800,22412864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489214738,0,false,-22413312,-22413248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545270654,0,true,33642304,33642368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477984898,0,false,-33643456,-33643392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626746,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627320,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275458603745,0,true,163211172480,163211172544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923564651807,0,false,-191733476352,-191733476288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275583552125,0,true,163318879232,163318879296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923439703427,0,false,-191882238592,-191882238528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071316089174,0,false,-28563359296,-28563359232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071356092564,0,false,-28522303872,-28522303808⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163182731520,163182731584⟩ : DyadicInterval 40),(⟨-191694200128,-191694200064⟩ : DyadicInterval 40),(⟨747990234382,747990253712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163299898304,163299898368⟩ : DyadicInterval 40),(⟨-191856020032,-191856019968⟩ : DyadicInterval 40),(⟨747968291104,747968310433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22413038,33642878⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22412800,22412864⟩ : DyadicInterval 40),(⟨-22413312,-22413248⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33642304,33642368⟩ : DyadicInterval 40),(⟨-33643456,-33643392⟩ : DyadicInterval 40),(⟨762123383098,762123402427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175946975969,176071924349⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163211172480,163211172544⟩ : DyadicInterval 40),(⟨-191733476352,-191733476288⟩ : DyadicInterval 40),(⟨747984909681,747984929010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163318879232,163318879296⟩ : DyadicInterval 40),(⟨-191882238592,-191882238528⟩ : DyadicInterval 40),(⟨747964734468,747964753797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28563359296,-28522303808⟩ : DyadicInterval 40),(⟨776384535520,776405082528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2331_ok : ecellOkT e2331 = true := by decide +kernel
theorem e2331_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2331 e2331_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '1999/2000', '7997/8000']  interval_lower 6803997/34359738368
noncomputable def e2332 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275517508383,0,true,163261950208,163261950272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923505747169,0,false,-191803605120,-191803605056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275653428245,0,true,163379108544,163379108608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923369827307,0,false,-191965441088,-191965441024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545269979,0,true,33641664,33641728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477985573,0,false,-33642752,-33642688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556514885,0,true,44886144,44886208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466740667,0,false,-44888064,-44888000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625943,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626747,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275561527448,0,true,163299894464,163299894528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923461728104,0,false,-191856014784,-191856014720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275686475808,0,true,163407592512,163407592576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923336779744,0,false,-192004793472,-192004793408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071283115866,0,false,-28597200960,-28597200896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071323142642,0,false,-28556120256,-28556120192⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163261950208,163261950272⟩ : DyadicInterval 40),(⟨-191803605120,-191803605056⟩ : DyadicInterval 40),(⟨747975400255,747975419585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163379108544,163379108608⟩ : DyadicInterval 40),(⟨-191965441088,-191965441024⟩ : DyadicInterval 40),(⟨747953445306,747953464635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33642203,44887109⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33641664,33641728⟩ : DyadicInterval 40),(⟨-33642752,-33642688⟩ : DyadicInterval 40),(⟨762123383066,762123402395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44886144,44886208⟩ : DyadicInterval 40),(⟨-44888064,-44888000⟩ : DyadicInterval 40),(⟨762123382679,762123402008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176049899672,176174848032⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163299894464,163299894528⟩ : DyadicInterval 40),(⟨-191856014784,-191856014720⟩ : DyadicInterval 40),(⟨747968291841,747968311170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163407592512,163407592576⟩ : DyadicInterval 40),(⟨-192004793472,-192004793408⟩ : DyadicInterval 40),(⟨747948104580,747948123909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28597200960,-28556120192⟩ : DyadicInterval 40),(⟨776401443712,776422003360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2332_ok : ecellOkT e2332 = true := by decide +kernel
theorem e2332_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2332 e2332_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '1999/2000', '7997/8000']  interval_lower 218924305/1099511627776
noncomputable def e2333 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275631402258,0,true,163360123712,163360123776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923391853294,0,false,-191939213760,-191939213696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275767336365,0,true,163477283840,163477283904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923255919187,0,false,-192101086656,-192101086592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545292577,0,true,33664256,33664320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477962975,0,false,-33665344,-33665280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556545020,0,true,44916288,44916352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466710532,0,false,-44918208,-44918144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625941,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626746,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275675449809,0,true,163398089152,163398089216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923347805743,0,false,-191991663808,-191991663744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275800405288,0,true,163505783744,163505783808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923222850264,0,false,-192140469376,-192140469312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071246594199,0,false,-28634685632,-28634685568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071286649150,0,false,-28593574592,-28593574528⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163360123712,163360123776⟩ : DyadicInterval 40),(⟨-191939213760,-191939213696⟩ : DyadicInterval 40),(⟨747957004323,747957023652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163477283840,163477283904⟩ : DyadicInterval 40),(⟨-192101086656,-192101086592⟩ : DyadicInterval 40),(⟨747935032635,747935051964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33664801,44917244⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33664256,33664320⟩ : DyadicInterval 40),(⟨-33665344,-33665280⟩ : DyadicInterval 40),(⟨762123383065,762123402394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44916288,44916352⟩ : DyadicInterval 40),(⟨-44918208,-44918144⟩ : DyadicInterval 40),(⟨762123382677,762123402006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176163822033,176288777512⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163398089152,163398089216⟩ : DyadicInterval 40),(⟨-191991663808,-191991663744⟩ : DyadicInterval 40),(⟨747949886614,747949905943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163505783744,163505783808⟩ : DyadicInterval 40),(⟨-192140469376,-192140469312⟩ : DyadicInterval 40),(⟨747929684917,747929704247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28634685632,-28593574528⟩ : DyadicInterval 40),(⟨776420170880,776440745696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2333_ok : ecellOkT e2333 = true := by decide +kernel
theorem e2333_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2333 e2333_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '7997/8000', '3999/4000']  interval_lower 217556497/1099511627776
noncomputable def e2334 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275539520124,0,true,163280924416,163280924480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923483735428,0,false,-191829812224,-191829812160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275675454230,0,true,163398092992,163398093056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923347801322,0,false,-191991669056,-191991668992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534055878,0,true,22427840,22427904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489199674,0,false,-22428352,-22428288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545293253,0,true,33664960,33665024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477962299,0,false,-33666048,-33665984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626745,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627319,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275572533229,0,true,163309381248,163309381312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923450722323,0,false,-191869118784,-191869118720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275697488734,0,true,163417084480,163417084544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923325766818,0,false,-192017907776,-192017907712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071279586552,0,false,-28600823296,-28600823232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071319618119,0,false,-28559737472,-28559737408⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163280924416,163280924480⟩ : DyadicInterval 40),(⟨-191829812224,-191829812160⟩ : DyadicInterval 40),(⟨747971845891,747971865221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163398092992,163398093056⟩ : DyadicInterval 40),(⟨-191991669056,-191991668992⟩ : DyadicInterval 40),(⟨747949885875,747949905205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22428102,33665477⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22427840,22427904⟩ : DyadicInterval 40),(⟨-22428352,-22428288⟩ : DyadicInterval 40),(⟨762123383350,762123402679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33664960,33665024⟩ : DyadicInterval 40),(⟨-33666048,-33665984⟩ : DyadicInterval 40),(⟨762123383065,762123402394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176060905453,176185860958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163309381248,163309381312⟩ : DyadicInterval 40),(⟨-191869118784,-191869118720⟩ : DyadicInterval 40),(⟨747966514256,747966533585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163417084480,163417084544⟩ : DyadicInterval 40),(⟨-192017907776,-192017907712⟩ : DyadicInterval 40),(⟨747946324592,747946343921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28600823296,-28559737408⟩ : DyadicInterval 40),(⟨776403252320,776423814528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2334_ok : ecellOkT e2334 = true := by decide +kernel
theorem e2334_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2334 e2334_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '7997/8000', '3999/4000']  interval_lower 218752655/1099511627776
noncomputable def e2335 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275653428243,0,true,163379108544,163379108608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923369827309,0,false,-191965441088,-191965441024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275789376593,0,true,163496278912,163496278976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923233878959,0,false,-192127334848,-192127334784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534070944,0,true,22442880,22442944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489184608,0,false,-22443456,-22443392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545315854,0,true,33687552,33687616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477939698,0,false,-33688640,-33688576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626743,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627318,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275686462713,0,true,163407581248,163407581312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923336792839,0,false,-192004777920,-192004777856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275811425338,0,true,163515280960,163515281024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923211830214,0,false,-192153593792,-192153593728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071243060318,0,false,-28638312768,-28638312704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071283120064,0,false,-28597196672,-28597196608⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163379108544,163379108608⟩ : DyadicInterval 40),(⟨-191965441088,-191965441024⟩ : DyadicInterval 40),(⟨747953445306,747953464636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163496278912,163496278976⟩ : DyadicInterval 40),(⟨-192127334848,-192127334784⟩ : DyadicInterval 40),(⟨747931468543,747931487873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22443168,33688078⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22442880,22442944⟩ : DyadicInterval 40),(⟨-22443456,-22443392⟩ : DyadicInterval 40),(⟨762123383381,762123402710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33687552,33687616⟩ : DyadicInterval 40),(⟨-33688640,-33688576⟩ : DyadicInterval 40),(⟨762123383063,762123402392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176174834937,176299797562⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163407581248,163407581312⟩ : DyadicInterval 40),(⟨-192004777920,-192004777856⟩ : DyadicInterval 40),(⟨747948106701,747948126030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163515280960,163515281024⟩ : DyadicInterval 40),(⟨-192153593792,-192153593728⟩ : DyadicInterval 40),(⟨747927902635,747927921964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28638312768,-28597196608⟩ : DyadicInterval 40),(⟨776421981920,776442559264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2335_ok : ecellOkT e2335 = true := by decide +kernel
theorem e2335_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2335 e2335_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '3999/4000', '7999/8000']  interval_lower 107501373/549755813888
noncomputable def e2336 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275333687138,0,true,163103482624,163103482688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923689568414,0,false,-191584772160,-191584772096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275469607000,0,true,163220657856,163220657920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923553648552,0,false,-191746575936,-191746575872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522826661,0,true,11198784,11198848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500428891,0,false,-11198976,-11198912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534041436,0,true,22413376,22413440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489214116,0,false,-22413952,-22413888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627319,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275355665824,0,true,163122431040,163122431104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923667589728,0,false,-191610934720,-191610934656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275480614229,0,true,163230146496,163230146560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923542641323,0,false,-191759680384,-191759680320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071349047762,0,false,-28529533824,-28529533760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071389027764,0,false,-28488503616,-28488503552⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175866025869,175979976721⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163103482624,163103482688⟩ : DyadicInterval 40),(⟨-191584772160,-191584772096⟩ : DyadicInterval 40),(⟨748005065207,748005084536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163220657856,163220657920⟩ : DyadicInterval 40),(⟨-191746575936,-191746575872⟩ : DyadicInterval 40),(⟨747983133580,747983152909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11198885,22413660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11198784,11198848⟩ : DyadicInterval 40),(⟨-11198976,-11198912⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22413376,22413440⟩ : DyadicInterval 40),(⟨-22413952,-22413888⟩ : DyadicInterval 40),(⟨762123383383,762123402712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175844038048,175968986453⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163122431040,163122431104⟩ : DyadicInterval 40),(⟨-191610934720,-191610934656⟩ : DyadicInterval 40),(⟨748001519977,748001539307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163230146496,163230146560⟩ : DyadicInterval 40),(⟨-191759680384,-191759680320⟩ : DyadicInterval 40),(⟨747981356761,747981376090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28529533824,-28488503552⟩ : DyadicInterval 40),(⟨776367635392,776388169792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2336_ok : ecellOkT e2336 = true := by decide +kernel
theorem e2336_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2336 e2336_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '3999/4000', '7999/8000']  interval_lower 108096211/549755813888
noncomputable def e2337 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275447609501,0,true,163201694848,163201694912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923575646051,0,false,-191720387712,-191720387648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275583543608,0,true,163318871872,163318871936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923439711944,0,false,-191882228416,-191882228352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522834193,0,true,11206336,11206400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500421359,0,false,-11206528,-11206464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534056500,0,true,22428480,22428544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489199052,0,false,-22428992,-22428928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627318,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275469602429,0,true,163220653888,163220653952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923553653123,0,false,-191746570496,-191746570432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275594557957,0,true,163328365824,163328365888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923428697595,0,false,-191895342976,-191895342912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071312564193,0,false,-28566977088,-28566977024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071352572372,0,false,-28525916544,-28525916480⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨175979976720,176093927572⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163201694848,163201694912⟩ : DyadicInterval 40),(⟨-191720387712,-191720387648⟩ : DyadicInterval 40),(⟨747986684206,747986703535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163318871872,163318871936⟩ : DyadicInterval 40),(⟨-191882228416,-191882228352⟩ : DyadicInterval 40),(⟨747964735840,747964755169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11206417,22428724⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11206336,11206400⟩ : DyadicInterval 40),(⟨-11206528,-11206464⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22428480,22428544⟩ : DyadicInterval 40),(⟨-22428992,-22428928⟩ : DyadicInterval 40),(⟨762123383350,762123402679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨175957974653,176082930181⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163220653888,163220653952⟩ : DyadicInterval 40),(⟨-191746570496,-191746570432⟩ : DyadicInterval 40),(⟨747983134335,747983153664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163328365824,163328365888⟩ : DyadicInterval 40),(⟨-191895342976,-191895342912⟩ : DyadicInterval 40),(⟨747962956695,747962976024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28566977088,-28525916480⟩ : DyadicInterval 40),(⟨776386341856,776406891424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2337_ok : ecellOkT e2337 = true := by decide +kernel
theorem e2337_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2337 e2337_ok ha1 ha2 hz1 hz2 hz

-- box ['40947/256000', '1311153/8192000', '7999/8000', '1']  interval_lower 214832439/1099511627776
noncomputable def e2338 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275377653645,0,true,163141387072,163141387136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923645601907,0,false,-191637108800,-191637108736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604497,0,true,163239620480,163239620544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651055,0,false,-191772764736,-191772764672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275355670391,0,true,163122435008,163122435072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923667585161,0,false,-191610940160,-191610940096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522834761,0,true,11206912,11206976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500420791,0,false,-11207104,-11207040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275366657412,0,true,163131907136,163131907200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923656598140,0,false,-191624018944,-191624018880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491612964,0,true,163239627776,163239627840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923531642588,0,false,-191772774848,-191772774784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071345527114,0,false,-28533147008,-28533146944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071385511902,0,false,-28492111808,-28492111744⟩
    { al := (40947/256000), au := (1311153/8192000), zl := (7999/8000), zu := 1,
      A := ⟨175866025869,175979976721⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163141387072,163141387136⟩ : DyadicInterval 40),(⟨-191637108800,-191637108736⟩ : DyadicInterval 40),(⟨747997972793,747997992123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163122435008,163122435072⟩ : DyadicInterval 40),(⟨-191610940160,-191610940096⟩ : DyadicInterval 40),(⟨748001519224,748001538554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11206985⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11206912,11206976⟩ : DyadicInterval 40),(⟨-11207104,-11207040⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175855029636,175979985188⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163131907136,163131907200⟩ : DyadicInterval 40),(⟨-191624018944,-191624018880⟩ : DyadicInterval 40),(⟨747999746803,747999766133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239627776,163239627840⟩ : DyadicInterval 40),(⟨-191772774848,-191772774784⟩ : DyadicInterval 40),(⟨747979581163,747979600493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28533147008,-28492111744⟩ : DyadicInterval 40),(⟨776369439488,776389976384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163141387072,163239620544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191772764736,-191637108736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2338_ok : ecellOkT e2338 = true := by decide +kernel
theorem e2338_pos {a z : ℝ} (ha1 : ((40947/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1311153/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2338 e2338_ok ha1 ha2 hz1 hz2 hz

-- box ['1311153/8192000', '656001/4096000', '7999/8000', '1']  interval_lower 216021835/1099511627776
noncomputable def e2339 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275491604496,0,true,163239620480,163239620544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923531651056,0,false,-191772764736,-191772764672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555348,0,true,163337845120,163337845184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700204,0,false,-191908437440,-191908437376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275469606998,0,true,163220657856,163220657920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923553648554,0,false,-191746575936,-191746575872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522842294,0,true,11214400,11214464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500413258,0,false,-11214592,-11214528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275480601140,0,true,163230135232,163230135296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923542654412,0,false,-191759664768,-191759664704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605563814,0,true,163337852416,163337852480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923417691738,0,false,-191908447552,-191908447488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071309038984,0,false,-28570595072,-28570595008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071349051952,0,false,-28529529536,-28529529472⟩
    { al := (1311153/8192000), au := (656001/4096000), zl := (7999/8000), zu := 1,
      A := ⟨175979976720,176093927572⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163239620480,163239620544⟩ : DyadicInterval 40),(⟨-191772764736,-191772764672⟩ : DyadicInterval 40),(⟨747979582515,747979601845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163220657856,163220657920⟩ : DyadicInterval 40),(⟨-191746575936,-191746575872⟩ : DyadicInterval 40),(⟨747983133580,747983152910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11214518⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11214400,11214464⟩ : DyadicInterval 40),(⟨-11214592,-11214528⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨175968973364,176093936038⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163230135232,163230135296⟩ : DyadicInterval 40),(⟨-191759664768,-191759664704⟩ : DyadicInterval 40),(⟨747981358849,747981378178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337852416,163337852480⟩ : DyadicInterval 40),(⟨-191908447552,-191908447488⟩ : DyadicInterval 40),(⟨747961178772,747961198101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28570595072,-28529529472⟩ : DyadicInterval 40),(⟨776388148352,776408700416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163239620480,163337845184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-191908437440,-191772764672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2339_ok : ecellOkT e2339 = true := by decide +kernel
theorem e2339_pos {a z : ℝ} (ha1 : ((1311153/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((656001/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2339 e2339_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B038

end


