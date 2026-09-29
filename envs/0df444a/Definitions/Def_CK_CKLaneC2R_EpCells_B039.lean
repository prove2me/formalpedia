-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B039
-- name    : CK_CKLaneC2R_EpCells_B039
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:24:14.866703+00:00
-- url     : https://prove2.me/theorems/676f0f2d-e17a-4809-b347-75fca63e9843
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B039` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B039` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B039` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B039 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B039.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B039 =====
section

namespace CKLaneC2R.EpCells.B039

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['656001/4096000', '1312851/8192000', '3999/4000', '7999/8000']  interval_lower 13586569/68719476736
noncomputable def e2340 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275561531865,0,true,163299898304,163299898368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923461723687,0,false,-191856020032,-191856019968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275697480215,0,true,163417077120,163417077184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923325775337,0,false,-192017897664,-192017897600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522841725,0,true,11213888,11213952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500413827,0,false,-11214016,-11213952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534071566,0,true,22443520,22443584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489183986,0,false,-22444032,-22443968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627317,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275583539033,0,true,163318867904,163318867968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923439716519,0,false,-191882222976,-191882222912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275708501685,0,true,163426576384,163426576448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923314753867,0,false,-192031022272,-192031022208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071276057008,0,false,-28604445824,-28604445760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071316093368,0,false,-28563355008,-28563354944⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176093927571,176207878423⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163299898304,163299898368⟩ : DyadicInterval 40),(⟨-191856020032,-191856019968⟩ : DyadicInterval 40),(⟨747968291104,747968310433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163417077120,163417077184⟩ : DyadicInterval 40),(⟨-192017897664,-192017897600⟩ : DyadicInterval 40),(⟨747946325993,747946345322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11213949,22443790⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11213888,11213952⟩ : DyadicInterval 40),(⟨-11214016,-11213952⟩ : DyadicInterval 40),(⟨762123383501,762123402830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22443520,22443584⟩ : DyadicInterval 40),(⟨-22444032,-22443968⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176071911257,176196873909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163318867904,163318867968⟩ : DyadicInterval 40),(⟨-191882222976,-191882222912⟩ : DyadicInterval 40),(⟨747964736596,747964755925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163426576384,163426576448⟩ : DyadicInterval 40),(⟨-192031022272,-192031022208⟩ : DyadicInterval 40),(⟨747944544491,747944563820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28604445824,-28563354944⟩ : DyadicInterval 40),(⟨776405061088,776425625792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2340_ok : ecellOkT e2340 = true := by decide +kernel
theorem e2340_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2340 e2340_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '3999/4000', '7999/8000']  interval_lower 218580715/1099511627776
noncomputable def e2341 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275675454228,0,true,163398092992,163398093056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923347801324,0,false,-191991669056,-191991668992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275811416822,0,true,163515273664,163515273728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923211838730,0,false,-192153583616,-192153583552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522849258,0,true,11221376,11221440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500406294,0,false,-11221568,-11221504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534086633,0,true,22458624,22458688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489168919,0,false,-22459136,-22459072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627317,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275697475640,0,true,163417073216,163417073280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923325779912,0,false,-192017892224,-192017892160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275822445415,0,true,163524778176,163524778240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923200810137,0,false,-192166718336,-192166718272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071239526207,0,false,-28641940096,-28641940032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071279590749,0,false,-28600818944,-28600818880⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176207878422,176321829274⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163398092992,163398093056⟩ : DyadicInterval 40),(⟨-191991669056,-191991668992⟩ : DyadicInterval 40),(⟨747949885875,747949905205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163515273664,163515273728⟩ : DyadicInterval 40),(⟨-192153583616,-192153583552⟩ : DyadicInterval 40),(⟨747927903973,747927923302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11221482,22458857⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11221376,11221440⟩ : DyadicInterval 40),(⟨-11221568,-11221504⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22458624,22458688⟩ : DyadicInterval 40),(⟨-22459136,-22459072⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176185847864,176310817639⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163417073216,163417073280⟩ : DyadicInterval 40),(⟨-192017892224,-192017892160⟩ : DyadicInterval 40),(⟨747946326712,747946346042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163524778176,163524778240⟩ : DyadicInterval 40),(⟨-192166718336,-192166718272⟩ : DyadicInterval 40),(⟨747926120175,747926139505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28641940096,-28600818880⟩ : DyadicInterval 40),(⟨776423793056,776444372928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2341_ok : ecellOkT e2341 = true := by decide +kernel
theorem e2341_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2341 e2341_ok ha1 ha2 hz1 hz2 hz

-- box ['656001/4096000', '1312851/8192000', '7999/8000', '1']  interval_lower 217214047/1099511627776
noncomputable def e2342 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275605555347,0,true,163337845120,163337845184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923417700205,0,false,-191908437440,-191908437376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506199,0,true,163436060992,163436061056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749353,0,false,-192044126848,-192044126784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275583543605,0,true,163318871872,163318871936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923439711947,0,false,-191882228416,-191882228352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522849827,0,true,11221952,11222016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500405725,0,false,-11222144,-11222080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275594544865,0,true,163328354560,163328354624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923428710687,0,false,-191895327360,-191895327296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719514670,0,true,163436068288,163436068352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923303740882,0,false,-192044136960,-192044136896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071272527234,0,false,-28608068672,-28608068608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071312568387,0,false,-28566972800,-28566972736⟩
    { al := (656001/4096000), au := (1312851/8192000), zl := (7999/8000), zu := 1,
      A := ⟨176093927571,176207878423⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163337845120,163337845184⟩ : DyadicInterval 40),(⟨-191908437440,-191908437376⟩ : DyadicInterval 40),(⟨747961180125,747961199455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163318871872,163318871936⟩ : DyadicInterval 40),(⟨-191882228416,-191882228352⟩ : DyadicInterval 40),(⟨747964735840,747964755170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11222051⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11221952,11222016⟩ : DyadicInterval 40),(⟨-11222144,-11222080⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176082917089,176207886894⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163328354560,163328354624⟩ : DyadicInterval 40),(⟨-191895327360,-191895327296⟩ : DyadicInterval 40),(⟨747962958786,747962978116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436068288,163436068352⟩ : DyadicInterval 40),(⟨-192044136960,-192044136896⟩ : DyadicInterval 40),(⟨747942764239,747942783568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28608068672,-28566972736⟩ : DyadicInterval 40),(⟨776406869984,776427437216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163337845120,163436061056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192044126848,-191908437376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2342_ok : ecellOkT e2342 = true := by decide +kernel
theorem e2342_pos {a z : ℝ} (ha1 : ((656001/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1312851/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2342 e2342_ok ha1 ha2 hz1 hz2 hz

-- box ['1312851/8192000', '13137/81920', '7999/8000', '1']  interval_lower 218409267/1099511627776
noncomputable def e2343 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275719506198,0,true,163436060992,163436061056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923303749354,0,false,-192044126848,-192044126784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457050,0,true,163534268032,163534268096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798502,0,false,-192179833024,-192179832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275697480213,0,true,163417077120,163417077184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923325775339,0,false,-192017897664,-192017897600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522857361,0,true,11229504,11229568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500398191,0,false,-11229696,-11229632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275708488591,0,true,163426565120,163426565184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923314766961,0,false,-192031006656,-192031006592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833465515,0,true,163534275328,163534275392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923189790037,0,false,-192179843136,-192179843072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071235991867,0,false,-28645567744,-28645567680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071276061206,0,false,-28604441536,-28604441472⟩
    { al := (1312851/8192000), au := (13137/81920), zl := (7999/8000), zu := 1,
      A := ⟨176207878422,176321829274⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163436060992,163436061056⟩ : DyadicInterval 40),(⟨-192044126848,-192044126784⟩ : DyadicInterval 40),(⟨747942765595,747942784925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163417077120,163417077184⟩ : DyadicInterval 40),(⟨-192017897664,-192017897600⟩ : DyadicInterval 40),(⟨747946325993,747946345322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11229585⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11229504,11229568⟩ : DyadicInterval 40),(⟨-11229696,-11229632⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176196860815,176321837739⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163426565120,163426565184⟩ : DyadicInterval 40),(⟨-192031006656,-192031006592⟩ : DyadicInterval 40),(⟨747944546585,747944565915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534275328,163534275392⟩ : DyadicInterval 40),(⟨-192179843136,-192179843072⟩ : DyadicInterval 40),(⟨747924337630,747924356959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28645567744,-28604441472⟩ : DyadicInterval 40),(⟨776425604352,776446186752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163436060992,163534268096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192179833024,-192044126784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2343_ok : ecellOkT e2343 = true := by decide +kernel
theorem e2343_pos {a z : ℝ} (ha1 : ((1312851/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((13137/81920 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2343 e2343_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '1999/2000', '7997/8000']  interval_lower 220123517/1099511627776
noncomputable def e2344 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275745296134,0,true,163458288448,163458288512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923277959418,0,false,-192074839104,-192074839040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275881244484,0,true,163575450432,163575450496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923142011068,0,false,-192236748992,-192236748928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545315177,0,true,33686848,33686912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477940375,0,false,-33687936,-33687872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556575156,0,true,44946432,44946496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466680396,0,false,-44948352,-44948288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625938,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626744,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275789372167,0,true,163496275072,163496275136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923233883385,0,false,-192127329536,-192127329472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275914334774,0,true,163603966144,163603966208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923108920778,0,false,-192276161984,-192276161920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071210048920,0,false,-28672195776,-28672195712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071250132052,0,false,-28631054400,-28631054336⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163458288448,163458288512⟩ : DyadicInterval 40),(⟨-192074839104,-192074839040⟩ : DyadicInterval 40),(⟨747938596274,747938615603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163575450432,163575450496⟩ : DyadicInterval 40),(⟨-192236748992,-192236748928⟩ : DyadicInterval 40),(⟨747916607830,747916627159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33687401,44947380⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33686848,33686912⟩ : DyadicInterval 40),(⟨-33687936,-33687872⟩ : DyadicInterval 40),(⟨762123383063,762123402392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44946432,44946496⟩ : DyadicInterval 40),(⟨-44948352,-44948288⟩ : DyadicInterval 40),(⟨762123382674,762123402003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176277744391,176402706998⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163496275072,163496275136⟩ : DyadicInterval 40),(⟨-192127329536,-192127329472⟩ : DyadicInterval 40),(⟨747931469257,747931488586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163603966144,163603966208⟩ : DyadicInterval 40),(⟨-192276161984,-192276161920⟩ : DyadicInterval 40),(⟨747911253157,747911272486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28672195776,-28631054336⟩ : DyadicInterval 40),(⟨776438910784,776459500768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2344_ok : ecellOkT e2344 = true := by decide +kernel
theorem e2344_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2344 e2344_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '1999/2000', '7997/8000']  interval_lower 110662839/549755813888
noncomputable def e2345 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275859190009,0,true,163556444480,163556444544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923164065543,0,false,-192210481216,-192210481152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275995152603,0,true,163673608256,163673608320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923028102949,0,false,-192372428032,-192372427968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545337779,0,true,33709440,33709504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477917773,0,false,-33710528,-33710464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556605293,0,true,44976576,44976640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466650259,0,false,-44978496,-44978432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625936,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626743,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275903294531,0,true,163594452288,163594452352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923119961021,0,false,-192263012096,-192263012032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276028264264,0,true,163702139840,163702139904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922994991288,0,false,-192411871360,-192411871296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071173480029,0,false,-28709731456,-28709731392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071213591344,0,false,-28668559744,-28668559680⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163556444480,163556444544⟩ : DyadicInterval 40),(⟨-192210481216,-192210481152⟩ : DyadicInterval 40),(⟨747920176097,747920195426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163673608256,163673608320⟩ : DyadicInterval 40),(⟨-192372428032,-192372427968⟩ : DyadicInterval 40),(⟨747898170899,747898190229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33710003,44977517⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33709440,33709504⟩ : DyadicInterval 40),(⟨-33710528,-33710464⟩ : DyadicInterval 40),(⟨762123383062,762123402391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44976576,44976640⟩ : DyadicInterval 40),(⟨-44978496,-44978432⟩ : DyadicInterval 40),(⟨762123382672,762123402001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176391666755,176516636488⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163594452288,163594452352⟩ : DyadicInterval 40),(⟨-192263012096,-192263012032⟩ : DyadicInterval 40),(⟨747913039786,747913059115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163702139840,163702139904⟩ : DyadicInterval 40),(⟨-192411871360,-192411871296⟩ : DyadicInterval 40),(⟨747892809251,747892828580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28709731456,-28668559680⟩ : DyadicInterval 40),(⟨776457663456,776478268608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2345_ok : ecellOkT e2345 = true := by decide +kernel
theorem e2345_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2345 e2345_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '7997/8000', '3999/4000']  interval_lower 219951295/1099511627776
noncomputable def e2346 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275767336362,0,true,163477283840,163477283904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923255919190,0,false,-192101086656,-192101086592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275903298957,0,true,163594456064,163594456128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923119956595,0,false,-192263017344,-192263017280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534086011,0,true,22457984,22458048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489169541,0,false,-22458496,-22458432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545338455,0,true,33710144,33710208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477917097,0,false,-33711232,-33711168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626742,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627318,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275800392191,0,true,163505772416,163505772480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923222863361,0,false,-192140453760,-192140453696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275925361946,0,true,163613468736,163613468800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923097893606,0,false,-192289296512,-192289296448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071206510469,0,false,-28675827712,-28675827648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071246598400,0,false,-28634681280,-28634681216⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163477283840,163477283904⟩ : DyadicInterval 40),(⟨-192101086656,-192101086592⟩ : DyadicInterval 40),(⟨747935032635,747935051965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163594456064,163594456128⟩ : DyadicInterval 40),(⟨-192263017344,-192263017280⟩ : DyadicInterval 40),(⟨747913039082,747913058411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22458235,33710679⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22457984,22458048⟩ : DyadicInterval 40),(⟨-22458496,-22458432⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33710144,33710208⟩ : DyadicInterval 40),(⟨-33711232,-33711168⟩ : DyadicInterval 40),(⟨762123383062,762123402391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176288764415,176413734170⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163505772416,163505772480⟩ : DyadicInterval 40),(⟨-192140453760,-192140453696⟩ : DyadicInterval 40),(⟨747929687051,747929706381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163613468736,163613468800⟩ : DyadicInterval 40),(⟨-192289296512,-192289296448⟩ : DyadicInterval 40),(⟨747909468503,747909487833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28675827712,-28634681216⟩ : DyadicInterval 40),(⟨776440724224,776461316736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2346_ok : ecellOkT e2346 = true := by decide +kernel
theorem e2346_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2346 e2346_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '7997/8000', '3999/4000']  interval_lower 221153129/1099511627776
noncomputable def e2347 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275881244482,0,true,163575450432,163575450496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923142011070,0,false,-192236748992,-192236748928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276017221320,0,true,163692624448,163692624512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923006034232,0,false,-192398716608,-192398716544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534101079,0,true,22473024,22473088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489154473,0,false,-22473536,-22473472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545361059,0,true,33732736,33732800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477894493,0,false,-33733824,-33733760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626741,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627317,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275914321675,0,true,163603954880,163603954944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923108933877,0,false,-192276146368,-192276146304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276039298556,0,true,163711647680,163711647744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922983956996,0,false,-192425015936,-192425015872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071169937007,0,false,-28713368256,-28713368192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071210053124,0,false,-28672191488,-28672191424⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163575450432,163575450496⟩ : DyadicInterval 40),(⟨-192236748992,-192236748928⟩ : DyadicInterval 40),(⟨747916607830,747916627159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163692624448,163692624512⟩ : DyadicInterval 40),(⟨-192398716608,-192398716544⟩ : DyadicInterval 40),(⟨747894597515,747894616845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22473303,33733283⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22473024,22473088⟩ : DyadicInterval 40),(⟨-22473536,-22473472⟩ : DyadicInterval 40),(⟨762123383348,762123402677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33732736,33732800⟩ : DyadicInterval 40),(⟨-33733824,-33733760⟩ : DyadicInterval 40),(⟨762123383061,762123402390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176402693899,176527670780⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163603954880,163603954944⟩ : DyadicInterval 40),(⟨-192276146368,-192276146304⟩ : DyadicInterval 40),(⟨747911255257,747911274586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163711647680,163711647744⟩ : DyadicInterval 40),(⟨-192425015936,-192425015872⟩ : DyadicInterval 40),(⟨747891022270,747891041600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28713368256,-28672191424⟩ : DyadicInterval 40),(⟨776459479328,776480087008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2347_ok : ecellOkT e2347 = true := by decide +kernel
theorem e2347_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2347 e2347_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '1999/2000', '7997/8000']  interval_lower 13908177/68719476736
noncomputable def e2348 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275973083885,0,true,163654591680,163654591744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923050171667,0,false,-192346140032,-192346139968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276109060723,0,true,163771757312,163771757376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922914194829,0,false,-192508123776,-192508123712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545360382,0,true,33732032,33732096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477895170,0,false,-33733184,-33733120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556635434,0,true,45006720,45006784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466620118,0,false,-45008640,-45008576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625933,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626742,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276017216895,0,true,163692620672,163692620736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923006038657,0,false,-192398711296,-192398711232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276142193747,0,true,163800304768,163800304832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922881061805,0,false,-192547597440,-192547597376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071136887530,0,false,-28747292672,-28747292608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071177027029,0,false,-28706090624,-28706090560⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163654591680,163654591744⟩ : DyadicInterval 40),(⟨-192346140032,-192346139968⟩ : DyadicInterval 40),(⟨747901743838,747901763167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163771757312,163771757376⟩ : DyadicInterval 40),(⟨-192508123776,-192508123712⟩ : DyadicInterval 40),(⟨747879721842,747879741171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33732606,45007658⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33732032,33732096⟩ : DyadicInterval 40),(⟨-33733184,-33733120⟩ : DyadicInterval 40),(⟨762123383093,762123402422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45006720,45006784⟩ : DyadicInterval 40),(⟨-45008640,-45008576⟩ : DyadicInterval 40),(⟨762123382669,762123401998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176505589119,176630565971⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163692620672,163692620736⟩ : DyadicInterval 40),(⟨-192398711296,-192398711232⟩ : DyadicInterval 40),(⟨747894598193,747894617523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163800304768,163800304832⟩ : DyadicInterval 40),(⟨-192547597440,-192547597376⟩ : DyadicInterval 40),(⟨747874353210,747874372540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28747292672,-28706090560⟩ : DyadicInterval 40),(⟨776476428896,776497049216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2348_ok : ecellOkT e2348 = true := by decide +kernel
theorem e2348_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2348 e2348_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '1999/2000', '7997/8000']  interval_lower 223738713/1099511627776
noncomputable def e2349 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276086977761,0,true,163752730176,163752730240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922936277791,0,false,-192481815616,-192481815552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276222968842,0,true,163869897600,163869897664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922800286710,0,false,-192643836352,-192643836288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545382988,0,true,33754688,33754752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477872564,0,false,-33755776,-33755712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556665577,0,true,45036864,45036928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466589975,0,false,-45038784,-45038720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625931,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626740,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276131139252,0,true,163790780288,163790780352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922892116300,0,false,-192534427328,-192534427264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276256123233,0,true,163898460928,163898460992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922767132319,0,false,-192683340352,-192683340288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071100271419,0,false,-28784879424,-28784879360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071140439109,0,false,-28743647040,-28743646976⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163752730176,163752730240⟩ : DyadicInterval 40),(⟨-192481815616,-192481815552⟩ : DyadicInterval 40),(⟨747883299449,747883318778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163869897600,163869897664⟩ : DyadicInterval 40),(⟨-192643836352,-192643836288⟩ : DyadicInterval 40),(⟨747861260711,747861280040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33755212,45037801⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33754688,33754752⟩ : DyadicInterval 40),(⟨-33755776,-33755712⟩ : DyadicInterval 40),(⟨762123383059,762123402388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45036864,45036928⟩ : DyadicInterval 40),(⟨-45038784,-45038720⟩ : DyadicInterval 40),(⟨762123382667,762123401996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176619511476,176744495457⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163790780288,163790780352⟩ : DyadicInterval 40),(⟨-192534427328,-192534427264⟩ : DyadicInterval 40),(⟨747876144523,747876163852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163898460928,163898460992⟩ : DyadicInterval 40),(⟨-192683340352,-192683340288⟩ : DyadicInterval 40),(⟨747855885085,747855904414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28784879424,-28743646976⟩ : DyadicInterval 40),(⟨776495207104,776515842592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2349_ok : ecellOkT e2349 = true := by decide +kernel
theorem e2349_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2349 e2349_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '7997/8000', '3999/4000']  interval_lower 27794727/137438953472
noncomputable def e2350 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275995152601,0,true,163673608256,163673608320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923028102951,0,false,-192372428032,-192372427968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276131143683,0,true,163790784064,163790784128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922892111869,0,false,-192534432576,-192534432512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534116148,0,true,22488128,22488192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489139404,0,false,-22488640,-22488576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545383665,0,true,33755328,33755392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477871887,0,false,-33756416,-33756352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626739,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627317,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276028251161,0,true,163702128576,163702128640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922995004391,0,false,-192411855744,-192411855680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276153235160,0,true,163809817856,163809817920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922870020392,0,false,-192560752192,-192560752128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071133339933,0,false,-28750934272,-28750934208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071173484237,0,false,-28709727168,-28709727104⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163673608256,163673608320⟩ : DyadicInterval 40),(⟨-192372428032,-192372427968⟩ : DyadicInterval 40),(⟨747898170899,747898190229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163790784064,163790784128⟩ : DyadicInterval 40),(⟨-192534432576,-192534432512⟩ : DyadicInterval 40),(⟨747876143816,747876163146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22488372,33755889⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22488128,22488192⟩ : DyadicInterval 40),(⟨-22488640,-22488576⟩ : DyadicInterval 40),(⟨762123383348,762123402677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33755328,33755392⟩ : DyadicInterval 40),(⟨-33756416,-33756352⟩ : DyadicInterval 40),(⟨762123383059,762123402388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176516623385,176641607384⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163702128576,163702128640⟩ : DyadicInterval 40),(⟨-192411855744,-192411855680⟩ : DyadicInterval 40),(⟨747892811354,747892830684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163809817856,163809817920⟩ : DyadicInterval 40),(⟨-192560752192,-192560752128⟩ : DyadicInterval 40),(⟨747872563954,747872583283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28750934272,-28709727104⟩ : DyadicInterval 40),(⟨776478247168,776498870016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2350_ok : ecellOkT e2350 = true := by decide +kernel
theorem e2350_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2350 e2350_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '7997/8000', '3999/4000']  interval_lower 111782701/549755813888
noncomputable def e2351 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276109060721,0,true,163771757312,163771757376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922914194831,0,false,-192508123776,-192508123712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276245066046,0,true,163888934976,163888935040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922778189506,0,false,-192670165376,-192670165312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534131219,0,true,22503168,22503232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489124333,0,false,-22503680,-22503616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545406272,0,true,33777920,33777984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477849280,0,false,-33779072,-33779008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626738,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627316,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276142180643,0,true,163800293440,163800293504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922881074909,0,false,-192547581824,-192547581760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276267171771,0,true,163907979328,163907979392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922756083781,0,false,-192696505152,-192696505088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071096719244,0,false,-28788525824,-28788525760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071136891741,0,false,-28747288384,-28747288320⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163771757312,163771757376⟩ : DyadicInterval 40),(⟨-192508123776,-192508123712⟩ : DyadicInterval 40),(⟨747879721842,747879741172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163888934976,163888935040⟩ : DyadicInterval 40),(⟨-192670165376,-192670165312⟩ : DyadicInterval 40),(⟨747857678000,747857697329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22503443,33778496⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22503168,22503232⟩ : DyadicInterval 40),(⟨-22503680,-22503616⟩ : DyadicInterval 40),(⟨762123383347,762123402676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33777920,33777984⟩ : DyadicInterval 40),(⟨-33779072,-33779008⟩ : DyadicInterval 40),(⟨762123383090,762123402419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176630552867,176755543995⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163800293440,163800293504⟩ : DyadicInterval 40),(⟨-192547581824,-192547581760⟩ : DyadicInterval 40),(⟨747874355353,747874374683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163907979328,163907979392⟩ : DyadicInterval 40),(⟨-192696505152,-192696505088⟩ : DyadicInterval 40),(⟨747854093458,747854112787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28788525824,-28747288320⟩ : DyadicInterval 40),(⟨776497027776,776517665792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2351_ok : ecellOkT e2351 = true := by decide +kernel
theorem e2351_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2351 e2351_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '3999/4000', '7999/8000']  interval_lower 219779089/1099511627776
noncomputable def e2352 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275789376591,0,true,163496278912,163496278976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923233878961,0,false,-192127334848,-192127334784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1275925353429,0,true,163613461376,163613461440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨923097902123,0,false,-192289286336,-192289286272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522856791,0,true,11228928,11228992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500398761,0,false,-11229120,-11229056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534101702,0,true,22473664,22473728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489153850,0,false,-22474176,-22474112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627316,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275811412240,0,true,163515269696,163515269760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923211843312,0,false,-192153578176,-192153578112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1275936389144,0,true,163622971200,163622971264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨923086866408,0,false,-192302431168,-192302431104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071202971789,0,false,-28679459904,-28679459840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071243064519,0,false,-28638308416,-28638308352⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176321829273,176435780125⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163496278912,163496278976⟩ : DyadicInterval 40),(⟨-192127334848,-192127334784⟩ : DyadicInterval 40),(⟨747931468544,747931487873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163613461376,163613461440⟩ : DyadicInterval 40),(⟨-192289286336,-192289286272⟩ : DyadicInterval 40),(⟨747909469880,747909489210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11229015,22473926⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11228928,11228992⟩ : DyadicInterval 40),(⟨-11229120,-11229056⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22473664,22473728⟩ : DyadicInterval 40),(⟨-22474176,-22474112⟩ : DyadicInterval 40),(⟨762123383348,762123402677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176299784464,176424761368⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163515269696,163515269760⟩ : DyadicInterval 40),(⟨-192153578176,-192153578112⟩ : DyadicInterval 40),(⟨747927904732,747927924062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163622971200,163622971264⟩ : DyadicInterval 40),(⟨-192302431168,-192302431104⟩ : DyadicInterval 40),(⟨747907683747,747907703076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28679459904,-28638308352⟩ : DyadicInterval 40),(⟨776442537792,776463132832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2352_ok : ecellOkT e2352 = true := by decide +kernel
theorem e2352_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2352 e2352_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '3999/4000', '7999/8000']  interval_lower 220980555/1099511627776
noncomputable def e2353 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275903298954,0,true,163594456064,163594456128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923119956598,0,false,-192263017344,-192263017280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276039290036,0,true,163711640320,163711640384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922983965516,0,false,-192425005824,-192425005760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522864326,0,true,11236480,11236544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500391226,0,false,-11236608,-11236544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534116771,0,true,22488704,22488768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489138781,0,false,-22489280,-22489216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627316,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1275925348846,0,true,163613457408,163613457472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨923097906706,0,false,-192289280896,-192289280832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276050332874,0,true,163721155456,163721155520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922972922678,0,false,-192438160768,-192438160704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071166393755,0,false,-28717005248,-28717005184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071206514674,0,false,-28675823424,-28675823360⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176435780124,176549730976⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163594456064,163594456128⟩ : DyadicInterval 40),(⟨-192263017344,-192263017280⟩ : DyadicInterval 40),(⟨747913039082,747913058412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163711640320,163711640384⟩ : DyadicInterval 40),(⟨-192425005824,-192425005760⟩ : DyadicInterval 40),(⟨747891023677,747891043007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11236550,22488995⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11236480,11236544⟩ : DyadicInterval 40),(⟨-11236608,-11236544⟩ : DyadicInterval 40),(⟨762123383501,762123402830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22488704,22488768⟩ : DyadicInterval 40),(⟨-22489280,-22489216⟩ : DyadicInterval 40),(⟨762123383380,762123402709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176413721070,176538705098⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163613457408,163613457472⟩ : DyadicInterval 40),(⟨-192289280896,-192289280832⟩ : DyadicInterval 40),(⟨747909470641,747909489970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163721155456,163721155520⟩ : DyadicInterval 40),(⟨-192438160768,-192438160704⟩ : DyadicInterval 40),(⟨747889235204,747889254533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28717005248,-28675823360⟩ : DyadicInterval 40),(⟨776461295296,776481905504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2353_ok : ecellOkT e2353 = true := by decide +kernel
theorem e2353_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2353 e2353_ok ha1 ha2 hz1 hz2 hz

-- box ['13137/81920', '1314549/8192000', '7999/8000', '1']  interval_lower 219607143/1099511627776
noncomputable def e2354 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275833457049,0,true,163534268032,163534268096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923189798503,0,false,-192179833024,-192179832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407901,0,true,163632466368,163632466432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847651,0,false,-192315555968,-192315555904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275811416820,0,true,163515273664,163515273728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923211838732,0,false,-192153583616,-192153583552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522864894,0,true,11237056,11237120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500390658,0,false,-11237184,-11237120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275822432318,0,true,163524766912,163524766976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923200823234,0,false,-192166702720,-192166702656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947416368,0,true,163632473664,163632473728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨923075839184,0,false,-192315566080,-192315566016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071199432879,0,false,-28683092352,-28683092288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071239530408,0,false,-28641935808,-28641935744⟩
    { al := (13137/81920), au := (1314549/8192000), zl := (7999/8000), zu := 1,
      A := ⟨176321829273,176435780125⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163534268032,163534268096⟩ : DyadicInterval 40),(⟨-192179833024,-192179832960⟩ : DyadicInterval 40),(⟨747924338987,747924358316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163515273664,163515273728⟩ : DyadicInterval 40),(⟨-192153583616,-192153583552⟩ : DyadicInterval 40),(⟨747927903973,747927923303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11237118⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11237056,11237120⟩ : DyadicInterval 40),(⟨-11237184,-11237120⟩ : DyadicInterval 40),(⟨762123383501,762123402830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176310804542,176435788592⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163524766912,163524766976⟩ : DyadicInterval 40),(⟨-192166702720,-192166702656⟩ : DyadicInterval 40),(⟨747926122273,747926141602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632473664,163632473728⟩ : DyadicInterval 40),(⟨-192315566080,-192315566016⟩ : DyadicInterval 40),(⟨747905898866,747905918195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28683092352,-28641935744⟩ : DyadicInterval 40),(⟨776444351488,776464949056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163534268032,163632466432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192315555968,-192179832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2354_ok : ecellOkT e2354 = true := by decide +kernel
theorem e2354_pos {a z : ℝ} (ha1 : ((13137/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1314549/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2354 e2354_ok ha1 ha2 hz1 hz2 hz

-- box ['1314549/8192000', '657699/4096000', '7999/8000', '1']  interval_lower 6900255/34359738368
noncomputable def e2355 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1275947407900,0,true,163632466368,163632466432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨923075847652,0,false,-192315555968,-192315555904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358752,0,true,163730655936,163730656000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896800,0,false,-192451295616,-192451295552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1275925353427,0,true,163613461376,163613461440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923097902125,0,false,-192289286336,-192289286272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522872430,0,true,11244544,11244608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500383122,0,false,-11244736,-11244672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1275936376044,0,true,163622959936,163622960000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨923086879508,0,false,-192302415552,-192302415488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061367225,0,true,163730663232,163730663296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922961888327,0,false,-192451305728,-192451305664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071162850271,0,false,-28720642496,-28720642432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071202975994,0,false,-28679455616,-28679455552⟩
    { al := (1314549/8192000), au := (657699/4096000), zl := (7999/8000), zu := 1,
      A := ⟨176435780124,176549730976⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163632466368,163632466432⟩ : DyadicInterval 40),(⟨-192315555968,-192315555904⟩ : DyadicInterval 40),(⟨747905900225,747905919555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163613461376,163613461440⟩ : DyadicInterval 40),(⟨-192289286336,-192289286272⟩ : DyadicInterval 40),(⟨747909469881,747909489210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11244654⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11244544,11244608⟩ : DyadicInterval 40),(⟨-11244736,-11244672⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176424748268,176549739449⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163622959936,163622960000⟩ : DyadicInterval 40),(⟨-192302415552,-192302415488⟩ : DyadicInterval 40),(⟨747907685848,747907705177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730663232,163730663296⟩ : DyadicInterval 40),(⟨-192451305728,-192451305664⟩ : DyadicInterval 40),(⟨747887447958,747887467287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28720642496,-28679455552⟩ : DyadicInterval 40),(⟨776463111392,776483724128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163632466368,163730656000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192451295616,-192315555904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2355_ok : ecellOkT e2355 = true := by decide +kernel
theorem e2355_pos {a z : ℝ} (ha1 : ((1314549/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((657699/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2355 e2355_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '3999/4000', '7999/8000']  interval_lower 27773101/137438953472
noncomputable def e2356 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276017221318,0,true,163692624448,163692624512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨923006034234,0,false,-192398716608,-192398716544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276153226643,0,true,163809810560,163809810624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922870028909,0,false,-192560742016,-192560741952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522871861,0,true,11243968,11244032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500383691,0,false,-11244160,-11244096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534131842,0,true,22503808,22503872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489123710,0,false,-22504320,-22504256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627315,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627662,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276039285453,0,true,163711636416,163711636480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922983970099,0,false,-192425000320,-192425000256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276164276603,0,true,163819330944,163819331008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922858978949,0,false,-192573907072,-192573907008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071129792105,0,false,-28754576064,-28754576000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071169941215,0,false,-28713363904,-28713363840⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176549730975,176663681827⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163692624448,163692624512⟩ : DyadicInterval 40),(⟨-192398716608,-192398716544⟩ : DyadicInterval 40),(⟨747894597516,747894616845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163809810560,163809810624⟩ : DyadicInterval 40),(⟨-192560742016,-192560741952⟩ : DyadicInterval 40),(⟨747872565297,747872584627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11244085,22504066⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11243968,11244032⟩ : DyadicInterval 40),(⟨-11244160,-11244096⟩ : DyadicInterval 40),(⟨762123383533,762123402862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22503808,22503872⟩ : DyadicInterval 40),(⟨-22504320,-22504256⟩ : DyadicInterval 40),(⟨762123383347,762123402676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176527657677,176652648827⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163711636416,163711636480⟩ : DyadicInterval 40),(⟨-192425000320,-192425000256⟩ : DyadicInterval 40),(⟨747891024375,747891043704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163819330944,163819331008⟩ : DyadicInterval 40),(⟨-192573907072,-192573907008⟩ : DyadicInterval 40),(⟨747870774519,747870793848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28754576064,-28713363840⟩ : DyadicInterval 40),(⟨776480065536,776500690912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2356_ok : ecellOkT e2356 = true := by decide +kernel
theorem e2356_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2356 e2356_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '3999/4000', '7999/8000']  interval_lower 111695939/549755813888
noncomputable def e2357 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276131143681,0,true,163790784064,163790784128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922892111871,0,false,-192534432576,-192534432512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276267163250,0,true,163907971968,163907972032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922756092302,0,false,-192696495040,-192696494976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522879396,0,true,11251520,11251584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500376156,0,false,-11251712,-11251648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534146914,0,true,22518848,22518912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489108638,0,false,-22519424,-22519360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627314,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276153222055,0,true,163809806592,163809806656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922870033497,0,false,-192560736576,-192560736512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276278220330,0,true,163917497664,163917497728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922745035222,0,false,-192709670144,-192709670080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071093166839,0,false,-28792172480,-28792172416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071133344145,0,false,-28750929920,-28750929856⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176663681826,176777632678⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163790784064,163790784128⟩ : DyadicInterval 40),(⟨-192534432576,-192534432512⟩ : DyadicInterval 40),(⟨747876143816,747876163146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163907971968,163907972032⟩ : DyadicInterval 40),(⟨-192696495040,-192696494976⟩ : DyadicInterval 40),(⟨747854094868,747854114198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11251620,22519138⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11251520,11251584⟩ : DyadicInterval 40),(⟨-11251712,-11251648⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22518848,22518912⟩ : DyadicInterval 40),(⟨-22519424,-22519360⟩ : DyadicInterval 40),(⟨762123383378,762123402707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176641594279,176766592554⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163809806592,163809806656⟩ : DyadicInterval 40),(⟨-192560736576,-192560736512⟩ : DyadicInterval 40),(⟨747872566061,747872585390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163917497664,163917497728⟩ : DyadicInterval 40),(⟨-192709670144,-192709670080⟩ : DyadicInterval 40),(⟨747852301717,747852321047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28792172480,-28750929856⟩ : DyadicInterval 40),(⟨776498848544,776519489120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2357_ok : ecellOkT e2357 = true := by decide +kernel
theorem e2357_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2357 e2357_ok ha1 ha2 hz1 hz2 hz

-- box ['657699/4096000', '1316247/8192000', '7999/8000', '1']  interval_lower 27751489/137438953472
noncomputable def e2358 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276061358751,0,true,163730655936,163730656000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922961896801,0,false,-192451295616,-192451295552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309603,0,true,163828836672,163828836736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945949,0,false,-192587052096,-192587052032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276039290034,0,true,163711640320,163711640384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922983965518,0,false,-192425005824,-192425005760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522879965,0,true,11252096,11252160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500375587,0,false,-11252288,-11252224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276050319771,0,true,163721144192,163721144256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922972935781,0,false,-192438145152,-192438145088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175318067,0,true,163828843968,163828844032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922847937485,0,false,-192587062144,-192587062080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071126244048,0,false,-28758218176,-28758218112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071166397964,0,false,-28717000896,-28717000832⟩
    { al := (657699/4096000), au := (1316247/8192000), zl := (7999/8000), zu := 1,
      A := ⟨176549730975,176663681827⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163730655936,163730656000⟩ : DyadicInterval 40),(⟨-192451295616,-192451295552⟩ : DyadicInterval 40),(⟨747887449320,747887468649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163711640320,163711640384⟩ : DyadicInterval 40),(⟨-192425005824,-192425005760⟩ : DyadicInterval 40),(⟨747891023677,747891043007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986359,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11252189⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11252096,11252160⟩ : DyadicInterval 40),(⟨-11252288,-11252224⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176538691995,176663690291⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163721144192,163721144256⟩ : DyadicInterval 40),(⟨-192438145152,-192438145088⟩ : DyadicInterval 40),(⟨747889237308,747889256637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828843968,163828844032⟩ : DyadicInterval 40),(⟨-192587062144,-192587062080⟩ : DyadicInterval 40),(⟨747868984970,747869004300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28758218176,-28717000832⟩ : DyadicInterval 40),(⟨776481884032,776502511968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163730655936,163828836736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192587052096,-192451295552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2358_ok : ecellOkT e2358 = true := by decide +kernel
theorem e2358_pos {a z : ℝ} (ha1 : ((657699/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1316247/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2358 e2358_ok ha1 ha2 hz1 hz2 hz

-- box ['1316247/8192000', '164637/1024000', '7999/8000', '1']  interval_lower 111609347/549755813888
noncomputable def e2359 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276175309602,0,true,163828836672,163828836736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922847945950,0,false,-192587052096,-192587052032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260454,0,true,163927008704,163927008768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995098,0,false,-192722825280,-192722825216⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276153226641,0,true,163809810560,163809810624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922870028911,0,false,-192560742016,-192560741952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522887501,0,true,11259648,11259712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500368051,0,false,-11259840,-11259776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276164263497,0,true,163819319680,163819319744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922858992055,0,false,-192573891456,-192573891392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289268924,0,true,163927016000,163927016064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922733986628,0,false,-192722835392,-192722835328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071089614201,0,false,-28795819392,-28795819328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071129796317,0,false,-28754571776,-28754571712⟩
    { al := (1316247/8192000), au := (164637/1024000), zl := (7999/8000), zu := 1,
      A := ⟨176663681826,176777632678⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163828836672,163828836736⟩ : DyadicInterval 40),(⟨-192587052096,-192587052032⟩ : DyadicInterval 40),(⟨747868986360,747869005689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163809810560,163809810624⟩ : DyadicInterval 40),(⟨-192560742016,-192560741952⟩ : DyadicInterval 40),(⟨747872565298,747872584627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511215,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11259725⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11259648,11259712⟩ : DyadicInterval 40),(⟨-11259840,-11259776⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176652635721,176777641148⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163819319680,163819319744⟩ : DyadicInterval 40),(⟨-192573891456,-192573891392⟩ : DyadicInterval 40),(⟨747870776626,747870795956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927016000,163927016064⟩ : DyadicInterval 40),(⟨-192722835392,-192722835328⟩ : DyadicInterval 40),(⟨747850509850,747850529180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28795819392,-28754571712⟩ : DyadicInterval 40),(⟨776500669472,776521312576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163828836672,163927008768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192722825280,-192587052032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2359_ok : ecellOkT e2359 = true := by decide +kernel
theorem e2359_pos {a z : ℝ} (ha1 : ((1316247/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164637/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2359 e2359_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '999/1000', '7993/8000']  interval_lower 225643225/1099511627776
noncomputable def e2360 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276112482820,0,true,163774705792,163774705856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922910772732,0,false,-192512200704,-192512200640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276248431170,0,true,163891834048,163891834112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922774824382,0,false,-192674174976,-192674174912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590442274,0,true,78811648,78811712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432813278,0,false,-78817344,-78817280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601762544,0,true,90131072,90131136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421493008,0,false,-90138496,-90138432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620387,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622127,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276200867829,0,true,163850856576,163850856640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922822387723,0,false,-192617503424,-192617503360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276325830340,0,true,163958512832,163958512896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922697425212,0,false,-192766402112,-192766402048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071077856419,0,false,-28807889216,-28807889152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071118033055,0,false,-28766646784,-28766646720⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163774705792,163774705856⟩ : DyadicInterval 40),(⟨-192512200704,-192512200640⟩ : DyadicInterval 40),(⟨747879167425,747879186754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163891834048,163891834112⟩ : DyadicInterval 40),(⟨-192674174976,-192674174912⟩ : DyadicInterval 40),(⟨747857132374,747857151703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78814498,90134768⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78811648,78811712⟩ : DyadicInterval 40),(⟨-78817344,-78817280⟩ : DyadicInterval 40),(⟨762123380750,762123400079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90131072,90131136⟩ : DyadicInterval 40),(⟨-90138496,-90138432⟩ : DyadicInterval 40),(⟨762123379874,762123399204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176689240053,176814202564⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163850856576,163850856640⟩ : DyadicInterval 40),(⟨-192617503424,-192617503360⟩ : DyadicInterval 40),(⟨747864843606,747864862936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163958512832,163958512896⟩ : DyadicInterval 40),(⟨-192766402112,-192766402048⟩ : DyadicInterval 40),(⟨747844579516,747844598845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28807889216,-28766646720⟩ : DyadicInterval 40),(⟨776506706976,776527347488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2360_ok : ecellOkT e2360 = true := by decide +kernel
theorem e2360_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2360 e2360_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '999/1000', '7993/8000']  interval_lower 226858525/1099511627776
noncomputable def e2361 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276226319720,0,true,163872784448,163872784512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922796935832,0,false,-192647828928,-192647828864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276362282315,0,true,163989914560,163989914624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922660973237,0,false,-192809840128,-192809840064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590495025,0,true,78864384,78864448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432760527,0,false,-78870080,-78870016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601822838,0,true,90191360,90191424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421432714,0,false,-90198784,-90198720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620377,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622119,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276314761700,0,true,163948977536,163948977600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922708493852,0,false,-192753212480,-192753212416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276439731339,0,true,164056630336,164056630400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922583524213,0,false,-192902138048,-192902137984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071041211420,0,false,-28845507648,-28845507584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071081416239,0,false,-28804234880,-28804234816⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163872784448,163872784512⟩ : DyadicInterval 40),(⟨-192647828928,-192647828864⟩ : DyadicInterval 40),(⟨747860717484,747860736813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163989914560,163989914624⟩ : DyadicInterval 40),(⟨-192809840128,-192809840064⟩ : DyadicInterval 40),(⟨747838665642,747838684971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78867249,90195062⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78864384,78864448⟩ : DyadicInterval 40),(⟨-78870080,-78870016⟩ : DyadicInterval 40),(⟨762123380742,762123400072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90191360,90191424⟩ : DyadicInterval 40),(⟨-90198784,-90198720⟩ : DyadicInterval 40),(⟨762123379864,762123399194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176803133924,176928103563⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163948977536,163948977600⟩ : DyadicInterval 40),(⟨-192753212480,-192753212416⟩ : DyadicInterval 40),(⟨747846375001,747846394330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164056630336,164056630400⟩ : DyadicInterval 40),(⟨-192902138048,-192902137984⟩ : DyadicInterval 40),(⟨747826096461,747826115791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28845507648,-28804234816⟩ : DyadicInterval 40),(⟨776525501024,776546156704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2361_ok : ecellOkT e2361 = true := by decide +kernel
theorem e2361_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2361 e2361_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '7993/8000', '3997/4000']  interval_lower 112734925/549755813888
noncomputable def e2362 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276134580024,0,true,163793744832,163793744896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922888675528,0,false,-192538526592,-192538526528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276270542618,0,true,163910883328,163910883392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922752712934,0,false,-192700521728,-192700521664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579183185,0,true,67553280,67553344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444072367,0,false,-67557504,-67557440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590495920,0,true,78865280,78865344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432759632,0,false,-78870976,-78870912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622118,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623626,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276211916237,0,true,163860375296,163860375360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922811339315,0,false,-192630667328,-192630667264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276336885895,0,true,163968036800,163968036864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922686369657,0,false,-192779576256,-192779576192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071074300585,0,false,-28811539456,-28811539392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071114482032,0,false,-28770291968,-28770291904⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163793744832,163793744896⟩ : DyadicInterval 40),(⟨-192538526592,-192538526528⟩ : DyadicInterval 40),(⟨747875586990,747875606320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163910883328,163910883392⟩ : DyadicInterval 40),(⟨-192700521728,-192700521664⟩ : DyadicInterval 40),(⟨747853546832,747853566162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67555409,78868144⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67553280,67553344⟩ : DyadicInterval 40),(⟨-67557504,-67557440⟩ : DyadicInterval 40),(⟨762123381513,762123400842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78865280,78865344⟩ : DyadicInterval 40),(⟨-78870976,-78870912⟩ : DyadicInterval 40),(⟨762123380742,762123400071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176700288461,176825258119⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163860375296,163860375360⟩ : DyadicInterval 40),(⟨-192630667328,-192630667264⟩ : DyadicInterval 40),(⟨747863052578,747863071907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163968036800,163968036864⟩ : DyadicInterval 40),(⟨-192779576256,-192779576192⟩ : DyadicInterval 40),(⟨747842786001,747842805331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28811539456,-28770291904⟩ : DyadicInterval 40),(⟨776508529568,776529172608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2362_ok : ecellOkT e2362 = true := by decide +kernel
theorem e2362_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2362 e2362_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '7993/8000', '3997/4000']  interval_lower 113342443/549755813888
noncomputable def e2363 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276248431168,0,true,163891834048,163891834112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922774824384,0,false,-192674174976,-192674174912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276384408007,0,true,164008974400,164008974464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922638847545,0,false,-192836207104,-192836207040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579228400,0,true,67598528,67598592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444027152,0,false,-67602752,-67602688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590548676,0,true,78918016,78918080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432706876,0,false,-78923776,-78923712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622111,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623620,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276325817231,0,true,163958501568,163958501632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922697438321,0,false,-192766386496,-192766386432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276450794016,0,true,164066159552,164066159616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922572461536,0,false,-192915322368,-192915322304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071037651004,0,false,-28849162752,-28849162688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071077860636,0,false,-28807884864,-28807884800⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163891834048,163891834112⟩ : DyadicInterval 40),(⟨-192674174976,-192674174912⟩ : DyadicInterval 40),(⟨747857132374,747857151704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164008974400,164008974464⟩ : DyadicInterval 40),(⟨-192836207104,-192836207040⟩ : DyadicInterval 40),(⟨747835075444,747835094774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67600624,78920900⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67598528,67598592⟩ : DyadicInterval 40),(⟨-67602752,-67602688⟩ : DyadicInterval 40),(⟨762123381507,762123400836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78918016,78918080⟩ : DyadicInterval 40),(⟨-78923776,-78923712⟩ : DyadicInterval 40),(⟨762123380767,762123400096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176814189455,176939166240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163958501568,163958501632⟩ : DyadicInterval 40),(⟨-192766386496,-192766386432⟩ : DyadicInterval 40),(⟨747844581628,747844600957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164066159552,164066159616⟩ : DyadicInterval 40),(⟨-192915322368,-192915322304⟩ : DyadicInterval 40),(⟨747824300662,747824319992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28849162752,-28807884800⟩ : DyadicInterval 40),(⟨776527326016,776547984256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2363_ok : ecellOkT e2363 = true := by decide +kernel
theorem e2363_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2363 e2363_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '999/1000', '7993/8000']  interval_lower 114038463/549755813888
noncomputable def e2364 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276340156621,0,true,163970854400,163970854464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922683098931,0,false,-192783473856,-192783473792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276476133459,0,true,164087986304,164087986368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922547122093,0,false,-192945522048,-192945521984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590547781,0,true,78917120,78917184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432707771,0,false,-78922880,-78922816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601883134,0,true,90251648,90251712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421372418,0,false,-90259072,-90259008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620367,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622112,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276428655575,0,true,164047089792,164047089856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922594599977,0,false,-192888938304,-192888938240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276553632340,0,true,164154739072,164154739136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922469623212,0,false,-193037890752,-193037890688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071004542822,0,false,-28883151616,-28883151552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071044775826,0,false,-28841848512,-28841848448⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163970854400,163970854464⟩ : DyadicInterval 40),(⟨-192783473856,-192783473792⟩ : DyadicInterval 40),(⟨747842255406,747842274736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164087986304,164087986368⟩ : DyadicInterval 40),(⟨-192945522048,-192945521984⟩ : DyadicInterval 40),(⟨747820186830,747820206160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78920005,90255358⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78917120,78917184⟩ : DyadicInterval 40),(⟨-78922880,-78922816⟩ : DyadicInterval 40),(⟨762123380767,762123400096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90251648,90251712⟩ : DyadicInterval 40),(⟨-90259072,-90259008⟩ : DyadicInterval 40),(⟨762123379854,762123399184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176917027799,177042004564⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164047089792,164047089856⟩ : DyadicInterval 40),(⟨-192888938304,-192888938240⟩ : DyadicInterval 40),(⟨747827894261,747827913590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164154739072,164154739136⟩ : DyadicInterval 40),(⟨-193037890752,-193037890688⟩ : DyadicInterval 40),(⟨747807601305,747807620635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28883151616,-28841848448⟩ : DyadicInterval 40),(⟨776544307840,776564978688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2364_ok : ecellOkT e2364 = true := by decide +kernel
theorem e2364_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2364 e2364_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '999/1000', '7993/8000']  interval_lower 114649061/549755813888
noncomputable def e2365 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276453993521,0,true,164068915584,164068915648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922569262031,0,false,-192919135488,-192919135424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276589984603,0,true,164186049280,164186049344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922433270949,0,false,-193081220672,-193081220608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590600540,0,true,78969920,78969984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432655012,0,false,-78975616,-78975552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601943436,0,true,90311936,90312000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421312116,0,false,-90319424,-90319360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620357,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622104,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276542549454,0,true,164145193216,164145193280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922480706098,0,false,-193024680896,-193024680832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276667533336,0,true,164252839040,164252839104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922355722216,0,false,-193173660224,-193173660160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070967850628,0,false,-28920821120,-28920821056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071008111817,0,false,-28879487616,-28879487552⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164068915584,164068915648⟩ : DyadicInterval 40),(⟨-192919135488,-192919135424⟩ : DyadicInterval 40),(⟨747823781229,747823800559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164186049280,164186049344⟩ : DyadicInterval 40),(⟨-193081220672,-193081220608⟩ : DyadicInterval 40),(⟨747801695911,747801715241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78972764,90315660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78969920,78969984⟩ : DyadicInterval 40),(⟨-78975616,-78975552⟩ : DyadicInterval 40),(⟨762123380727,762123400056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90311936,90312000⟩ : DyadicInterval 40),(⟨-90319424,-90319360⟩ : DyadicInterval 40),(⟨762123379877,762123399206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177030921678,177155905560⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164145193216,164145193280⟩ : DyadicInterval 40),(⟨-193024680896,-193024680832⟩ : DyadicInterval 40),(⟨747809401459,747809420788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164252839040,164252839104⟩ : DyadicInterval 40),(⟨-193173660224,-193173660160⟩ : DyadicInterval 40),(⟨747789094047,747789113376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28920821120,-28879487552⟩ : DyadicInterval 40),(⟨776563127392,776583813440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2365_ok : ecellOkT e2365 = true := by decide +kernel
theorem e2365_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2365 e2365_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '7993/8000', '3997/4000']  interval_lower 227902785/1099511627776
noncomputable def e2366 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276362282313,0,true,163989914560,163989914624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922660973239,0,false,-192809840128,-192809840064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276498273395,0,true,164107056704,164107056768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922524982157,0,false,-192971909184,-192971909120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579273620,0,true,67643712,67643776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443981932,0,false,-67647936,-67647872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590601437,0,true,78970816,78970880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432654115,0,false,-78976512,-78976448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622103,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623615,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276439718228,0,true,164056619072,164056619136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922583537324,0,false,-192902122432,-192902122368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276564702140,0,true,164164273600,164164273664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922458553412,0,false,-193051085184,-193051085120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071000977820,0,false,-28886811520,-28886811456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071041215641,0,false,-28845503360,-28845503296⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163989914560,163989914624⟩ : DyadicInterval 40),(⟨-192809840128,-192809840064⟩ : DyadicInterval 40),(⟨747838665642,747838684971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164107056704,164107056768⟩ : DyadicInterval 40),(⟨-192971909184,-192971909120⟩ : DyadicInterval 40),(⟨747816591943,747816611273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67645844,78973661⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67643712,67643776⟩ : DyadicInterval 40),(⟨-67647936,-67647872⟩ : DyadicInterval 40),(⟨762123381502,762123400831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78970816,78970880⟩ : DyadicInterval 40),(⟨-78976512,-78976448⟩ : DyadicInterval 40),(⟨762123380727,762123400056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176928090452,177053074364⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164056619072,164056619136⟩ : DyadicInterval 40),(⟨-192902122432,-192902122368⟩ : DyadicInterval 40),(⟨747826098576,747826117906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164164273600,164164273664⟩ : DyadicInterval 40),(⟨-193051085184,-193051085120⟩ : DyadicInterval 40),(⟨747805803154,747805822483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28886811520,-28845503296⟩ : DyadicInterval 40),(⟨776546135264,776566808640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2366_ok : ecellOkT e2366 = true := by decide +kernel
theorem e2366_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2366 e2366_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '7993/8000', '3997/4000']  interval_lower 57280893/274877906944
noncomputable def e2367 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276476133457,0,true,164087986304,164087986368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922547122095,0,false,-192945522048,-192945521984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276612138783,0,true,164205130240,164205130304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922411116769,0,false,-193107628032,-193107627968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579318842,0,true,67688960,67689024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443936710,0,false,-67693184,-67693120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590654201,0,true,79023552,79023616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432601351,0,false,-79029312,-79029248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622096,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623609,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276553619225,0,true,164154727808,164154727872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922469636327,0,false,-193037875136,-193037875072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276678610259,0,true,164262378880,164262378944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922344645293,0,false,-193186864768,-193186864704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070964281036,0,false,-28924485824,-28924485760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071004547047,0,false,-28883147264,-28883147200⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164087986304,164087986368⟩ : DyadicInterval 40),(⟨-192945522048,-192945521984⟩ : DyadicInterval 40),(⟨747820186831,747820206160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164205130240,164205130304⟩ : DyadicInterval 40),(⟨-193107628032,-193107627968⟩ : DyadicInterval 40),(⟨747798096356,747798115685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67691066,79026425⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67688960,67689024⟩ : DyadicInterval 40),(⟨-67693184,-67693120⟩ : DyadicInterval 40),(⟨762123381496,762123400825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79023552,79023616⟩ : DyadicInterval 40),(⟨-79029312,-79029248⟩ : DyadicInterval 40),(⟨762123380751,762123400081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177041991449,177166982483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164154727808,164154727872⟩ : DyadicInterval 40),(⟨-193037875136,-193037875072⟩ : DyadicInterval 40),(⟨747807603423,747807622753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164262378880,164262378944⟩ : DyadicInterval 40),(⟨-193186864768,-193186864704⟩ : DyadicInterval 40),(⟨747787293541,747787312870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28924485824,-28883147200⟩ : DyadicInterval 40),(⟨776564957216,776585645792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2367_ok : ecellOkT e2367 = true := by decide +kernel
theorem e2367_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2367 e2367_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '3997/4000', '1599/1600']  interval_lower 225296729/1099511627776
noncomputable def e2368 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276156677228,0,true,163812783488,163812783552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922866578324,0,false,-192564853056,-192564852992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276292654066,0,true,163929932224,163929932288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922730601486,0,false,-192726869056,-192726868992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567924042,0,true,56294784,56294848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455331510,0,false,-56297728,-56297664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579229241,0,true,67599360,67599424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444026311,0,false,-67603584,-67603520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623619,0,false,-4160,-4096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624894,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276222964670,0,true,163869894016,163869894080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922800290882,0,false,-192643831360,-192643831296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276347941475,0,true,163977560704,163977560768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922675314077,0,false,-192792750656,-192792750592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071070744521,0,false,-28815189952,-28815189888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071110930778,0,false,-28773937344,-28773937280⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163812783488,163812783552⟩ : DyadicInterval 40),(⟨-192564853056,-192564852992⟩ : DyadicInterval 40),(⟨747872006110,747872025439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163929932224,163929932288⟩ : DyadicInterval 40),(⟨-192726869056,-192726868992⟩ : DyadicInterval 40),(⟨747849960843,747849980172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56296266,67601465⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56294784,56294848⟩ : DyadicInterval 40),(⟨-56297728,-56297664⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67599360,67599424⟩ : DyadicInterval 40),(⟨-67603584,-67603520⟩ : DyadicInterval 40),(⟨762123381507,762123400836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176711336894,176836313699⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163869894016,163869894080⟩ : DyadicInterval 40),(⟨-192643831360,-192643831296⟩ : DyadicInterval 40),(⟨747861261372,747861280702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163977560704,163977560768⟩ : DyadicInterval 40),(⟨-192792750656,-192792750592⟩ : DyadicInterval 40),(⟨747840992399,747841011728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28815189952,-28773937280⟩ : DyadicInterval 40),(⟨776510352256,776530997856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2368_ok : ecellOkT e2368 = true := by decide +kernel
theorem e2368_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2368 e2368_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '3997/4000', '1599/1600']  interval_lower 56627775/274877906944
noncomputable def e2369 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276270542616,0,true,163910883328,163910883392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922752712936,0,false,-192700521728,-192700521664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276406533699,0,true,164028033856,164028033920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922616721853,0,false,-192862574656,-192862574592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567961722,0,true,56332480,56332544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455293830,0,false,-56335424,-56335360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579274462,0,true,67644544,67644608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443981090,0,false,-67648768,-67648704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623614,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624890,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276336872786,0,true,163968025536,163968025600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922686382766,0,false,-192779560640,-192779560576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276461856717,0,true,164075688768,164075688832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922561398835,0,false,-192928506816,-192928506752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071034090357,0,false,-28852818048,-28852817984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071074304802,0,false,-28811535104,-28811535040⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163910883328,163910883392⟩ : DyadicInterval 40),(⟨-192700521728,-192700521664⟩ : DyadicInterval 40),(⟨747853546833,747853566162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164028033856,164028033920⟩ : DyadicInterval 40),(⟨-192862574656,-192862574592⟩ : DyadicInterval 40),(⟨747831484797,747831504127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56333946,67646686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56332480,56332544⟩ : DyadicInterval 40),(⟨-56335424,-56335360⟩ : DyadicInterval 40),(⟨762123382137,762123401466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67644544,67644608⟩ : DyadicInterval 40),(⟨-67648768,-67648704⟩ : DyadicInterval 40),(⟨762123381501,762123400831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176825245010,176950228941⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163968025536,163968025600⟩ : DyadicInterval 40),(⟨-192779560640,-192779560576⟩ : DyadicInterval 40),(⟨747842788113,747842807443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164075688768,164075688832⟩ : DyadicInterval 40),(⟨-192928506816,-192928506752⟩ : DyadicInterval 40),(⟨747822504684,747822524014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28852818048,-28811535040⟩ : DyadicInterval 40),(⟨776529151136,776549811904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2369_ok : ecellOkT e2369 = true := by decide +kernel
theorem e2369_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2369 e2369_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '1599/1600', '1999/2000']  interval_lower 56280761/274877906944
noncomputable def e2370 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276178774432,0,true,163831821888,163831821952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922844481120,0,false,-192591180224,-192591180160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276314765514,0,true,163948980864,163948980928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922708490038,0,false,-192753217024,-192753216960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556664846,0,true,45036096,45036160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466590706,0,false,-45038016,-45037952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567962508,0,true,56333248,56333312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455293044,0,false,-56336192,-56336128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624889,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625932,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276234013130,0,true,163879412608,163879412672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922789242422,0,false,-192656995648,-192656995584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276358997086,0,true,163987084544,163987084608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922664258466,0,false,-192805925248,-192805925184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071067188225,0,false,-28818840640,-28818840576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071107379294,0,false,-28777583040,-28777582976⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163831821888,163831821952⟩ : DyadicInterval 40),(⟨-192591180224,-192591180160⟩ : DyadicInterval 40),(⟨747868424761,747868444090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163948980864,163948980928⟩ : DyadicInterval 40),(⟨-192753217024,-192753216960⟩ : DyadicInterval 40),(⟨747846374357,747846393687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45037070,56334732⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45036096,45036160⟩ : DyadicInterval 40),(⟨-45038016,-45037952⟩ : DyadicInterval 40),(⟨762123382667,762123401996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56333248,56333312⟩ : DyadicInterval 40),(⟨-56336192,-56336128⟩ : DyadicInterval 40),(⟨762123382137,762123401466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176722385354,176847369310⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163879412608,163879412672⟩ : DyadicInterval 40),(⟨-192656995648,-192656995584⟩ : DyadicInterval 40),(⟨747859470115,747859489445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163987084544,163987084608⟩ : DyadicInterval 40),(⟨-192805925248,-192805925184⟩ : DyadicInterval 40),(⟨747839198681,747839218010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28818840640,-28777582976⟩ : DyadicInterval 40),(⟨776512175104,776532823200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2370_ok : ecellOkT e2370 = true := by decide +kernel
theorem e2370_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2370 e2370_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '1599/1600', '1999/2000']  interval_lower 113168479/549755813888
noncomputable def e2371 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276292654064,0,true,163929932224,163929932288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922730601488,0,false,-192726869056,-192726868992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276428659390,0,true,164047093056,164047093120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922594596162,0,false,-192888942848,-192888942784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556694989,0,true,45066240,45066304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466560563,0,false,-45068160,-45068096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568000192,0,true,56370944,56371008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455255360,0,false,-56373888,-56373824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624885,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625929,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276347928365,0,true,163977549376,163977549440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922675327187,0,false,-192792735040,-192792734976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276472919449,0,true,164085217856,164085217920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922550336103,0,false,-192941691520,-192941691456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071030529477,0,false,-28856473600,-28856473536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071070748739,0,false,-28815185600,-28815185536⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163929932224,163929932288⟩ : DyadicInterval 40),(⟨-192726869056,-192726868992⟩ : DyadicInterval 40),(⟨747849960843,747849980173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164047093056,164047093120⟩ : DyadicInterval 40),(⟨-192888942848,-192888942784⟩ : DyadicInterval 40),(⟨747827893653,747827912983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45067213,56372416⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45066240,45066304⟩ : DyadicInterval 40),(⟨-45068160,-45068096⟩ : DyadicInterval 40),(⟨762123382664,762123401993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56370944,56371008⟩ : DyadicInterval 40),(⟨-56373888,-56373824⟩ : DyadicInterval 40),(⟨762123382133,762123401462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176836300589,176961291673⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163977549376,163977549440⟩ : DyadicInterval 40),(⟨-192792735040,-192792734976⟩ : DyadicInterval 40),(⟨747840994548,747841013878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164085217856,164085217920⟩ : DyadicInterval 40),(⟨-192941691520,-192941691456⟩ : DyadicInterval 40),(⟨747820708654,747820727984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28856473600,-28815185536⟩ : DyadicInterval 40),(⟨776530976384,776551639680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2371_ok : ecellOkT e2371 = true := by decide +kernel
theorem e2371_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2371 e2371_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '3997/4000', '1599/1600']  interval_lower 227728505/1099511627776
noncomputable def e2372 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276384408005,0,true,164008974400,164008974464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922638847547,0,false,-192836207104,-192836207040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276520413330,0,true,164126126784,164126126848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922502842222,0,false,-192998297024,-192998296960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567999405,0,true,56370176,56370240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455256147,0,false,-56373120,-56373056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579319685,0,true,67689792,67689856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443935867,0,false,-67694016,-67693952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623608,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624886,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276450780903,0,true,164066148288,164066148352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922572474649,0,false,-192915306688,-192915306624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276575771963,0,true,164173808064,164173808128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922447483589,0,false,-193064279744,-193064279680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070997412587,0,false,-28890471680,-28890471616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071037655225,0,false,-28849158400,-28849158336⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164008974400,164008974464⟩ : DyadicInterval 40),(⟨-192836207104,-192836207040⟩ : DyadicInterval 40),(⟨747835075445,747835094774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164126126784,164126126848⟩ : DyadicInterval 40),(⟨-192998297024,-192998296960⟩ : DyadicInterval 40),(⟨747812996623,747813015952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56371629,67691909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56370176,56370240⟩ : DyadicInterval 40),(⟨-56373120,-56373056⟩ : DyadicInterval 40),(⟨762123382133,762123401462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67689792,67689856⟩ : DyadicInterval 40),(⟨-67694016,-67693952⟩ : DyadicInterval 40),(⟨762123381496,762123400825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176939153127,177064144187⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164066148288,164066148352⟩ : DyadicInterval 40),(⟨-192915306688,-192915306624⟩ : DyadicInterval 40),(⟨747824302751,747824322080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164173808064,164173808128⟩ : DyadicInterval 40),(⟨-193064279744,-193064279680⟩ : DyadicInterval 40),(⟨747804004861,747804024191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28890471680,-28849158336⟩ : DyadicInterval 40),(⟨776547962784,776568638720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2372_ok : ecellOkT e2372 = true := by decide +kernel
theorem e2372_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2372 e2372_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '3997/4000', '1599/1600']  interval_lower 228948897/1099511627776
noncomputable def e2373 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276498273393,0,true,164107056704,164107056768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922524982159,0,false,-192971909184,-192971909120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276634292962,0,true,164224210880,164224210944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922388962590,0,false,-193134036096,-193134036032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568037092,0,true,56407808,56407872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455218460,0,false,-56410816,-56410752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579364911,0,true,67735040,67735104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443890641,0,false,-67739264,-67739200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623602,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624882,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276564689026,0,true,164164262336,164164262400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922458566526,0,false,-193051069504,-193051069440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276689687204,0,true,164271918592,164271918656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922333568348,0,false,-193200069440,-193200069376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070960711214,0,false,-28928150848,-28928150784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071000982044,0,false,-28886807168,-28886807104⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164107056704,164107056768⟩ : DyadicInterval 40),(⟨-192971909184,-192971909120⟩ : DyadicInterval 40),(⟨747816591944,747816611273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164224210880,164224210944⟩ : DyadicInterval 40),(⟨-193134036096,-193134036032⟩ : DyadicInterval 40),(⟨747794496365,747794515695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56409316,67737135⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56407808,56407872⟩ : DyadicInterval 40),(⟨-56410816,-56410752⟩ : DyadicInterval 40),(⟨762123382161,762123401491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67735040,67735104⟩ : DyadicInterval 40),(⟨-67739264,-67739200⟩ : DyadicInterval 40),(⟨762123381490,762123400820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177053061250,177178059428⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164164262336,164164262400⟩ : DyadicInterval 40),(⟨-193051069504,-193051069440⟩ : DyadicInterval 40),(⟨747805805246,747805824575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164271918592,164271918656⟩ : DyadicInterval 40),(⟨-193200069440,-193200069376⟩ : DyadicInterval 40),(⟨747785492930,747785512260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28928150848,-28886807104⟩ : DyadicInterval 40),(⟨776566787168,776587478304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2373_ok : ecellOkT e2373 = true := by decide +kernel
theorem e2373_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2373 e2373_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '1599/1600', '1999/2000']  interval_lower 113776985/549755813888
noncomputable def e2374 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276406533696,0,true,164028033856,164028033920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922616721856,0,false,-192862574656,-192862574592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276542553266,0,true,164145196480,164145196544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922480702286,0,false,-193024685440,-193024685376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556725136,0,true,45096384,45096448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466530416,0,false,-45098304,-45098240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568037879,0,true,56408640,56408704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455217673,0,false,-56411584,-56411520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624881,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625927,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276461843604,0,true,164075677440,164075677504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922561411948,0,false,-192928491200,-192928491136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276586841812,0,true,164183342464,164183342528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922436413740,0,false,-193077474560,-193077474496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070993847123,0,false,-28894132096,-28894132032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071034094579,0,false,-28852813696,-28852813632⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164028033856,164028033920⟩ : DyadicInterval 40),(⟨-192862574656,-192862574592⟩ : DyadicInterval 40),(⟨747831484797,747831504127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164145196480,164145196544⟩ : DyadicInterval 40),(⟨-193024685440,-193024685376⟩ : DyadicInterval 40),(⟨747809400851,747809420180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45097360,56410103⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45096384,45096448⟩ : DyadicInterval 40),(⟨-45098304,-45098240⟩ : DyadicInterval 40),(⟨762123382662,762123401991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56408640,56408704⟩ : DyadicInterval 40),(⟨-56411584,-56411520⟩ : DyadicInterval 40),(⟨762123382129,762123401458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176950215828,177075214036⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164075677440,164075677504⟩ : DyadicInterval 40),(⟨-192928491200,-192928491136⟩ : DyadicInterval 40),(⟨747822506837,747822526166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164183342464,164183342528⟩ : DyadicInterval 40),(⟨-193077474560,-193077474496⟩ : DyadicInterval 40),(⟨747802206480,747802225809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28894132096,-28852813632⟩ : DyadicInterval 40),(⟨776549790432,776570468928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2374_ok : ecellOkT e2374 = true := by decide +kernel
theorem e2374_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2374 e2374_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '1599/1600', '1999/2000']  interval_lower 228773969/1099511627776
noncomputable def e2375 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276520413328,0,true,164126126784,164126126848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922502842224,0,false,-192998297024,-192998296960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276656447142,0,true,164243291200,164243291264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922366808410,0,false,-193160444800,-193160444736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556755285,0,true,45126528,45126592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466500267,0,false,-45128448,-45128384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568075568,0,true,56446336,56446400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455179984,0,false,-56449280,-56449216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624878,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625924,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276575758848,0,true,164173796736,164173796800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922447496704,0,false,-193064264128,-193064264064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276700764177,0,true,164281458304,164281458368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922322491375,0,false,-193213274368,-193213274304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070957141160,0,false,-28931816064,-28931816000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070997416812,0,false,-28890467328,-28890467264⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164126126784,164126126848⟩ : DyadicInterval 40),(⟨-192998297024,-192998296960⟩ : DyadicInterval 40),(⟨747812996623,747813015952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164243291200,164243291264⟩ : DyadicInterval 40),(⟨-193160444800,-193160444736⟩ : DyadicInterval 40),(⟨747790895912,747790915241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45127509,56447792⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45126528,45126592⟩ : DyadicInterval 40),(⟨-45128448,-45128384⟩ : DyadicInterval 40),(⟨762123382659,762123401988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56446336,56446400⟩ : DyadicInterval 40),(⟨-56449280,-56449216⟩ : DyadicInterval 40),(⟨762123382125,762123401455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177064131072,177189136401⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164173796736,164173796800⟩ : DyadicInterval 40),(⟨-193064264128,-193064264064⟩ : DyadicInterval 40),(⟨747804007017,747804026347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164281458304,164281458368⟩ : DyadicInterval 40),(⟨-193213274368,-193213274304⟩ : DyadicInterval 40),(⟨747783692193,747783711522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28931816064,-28890467264⟩ : DyadicInterval 40),(⟨776568617248,776589310912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2375_ok : ecellOkT e2375 = true := by decide +kernel
theorem e2375_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2375 e2375_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '999/1000', '7993/8000']  interval_lower 230522081/1099511627776
noncomputable def e2376 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276567830421,0,true,164166968000,164166968064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922455425131,0,false,-193054813888,-193054813824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276703835747,0,true,164284103552,164284103616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922319419805,0,false,-193216936064,-193216936000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590653304,0,true,79022656,79022720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432602248,0,false,-79028416,-79028352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602003742,0,true,90372224,90372288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421251810,0,false,-90379712,-90379648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620347,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622097,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276656443327,0,true,164243287936,164243288000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922366812225,0,false,-193160440256,-193160440192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276781434336,0,true,164350930304,164350930368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922241821216,0,false,-193309446464,-193309446400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070931134833,0,false,-28958516096,-28958516032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070971424214,0,false,-28917152256,-28917152192⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164166968000,164166968064⟩ : DyadicInterval 40),(⟨-193054813888,-193054813824⟩ : DyadicInterval 40),(⟨747805294978,747805314307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164284103552,164284103616⟩ : DyadicInterval 40),(⟨-193216936064,-193216936000⟩ : DyadicInterval 40),(⟨747783192873,747783212203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79025528,90375966⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79022656,79022720⟩ : DyadicInterval 40),(⟨-79028416,-79028352⟩ : DyadicInterval 40),(⟨762123380751,762123400081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90372224,90372288⟩ : DyadicInterval 40),(⟨-90379712,-90379648⟩ : DyadicInterval 40),(⟨762123379867,762123399196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177144815551,177269806560⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164243287936,164243288000⟩ : DyadicInterval 40),(⟨-193160440256,-193160440192⟩ : DyadicInterval 40),(⟨747790896521,747790915850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164350930304,164350930368⟩ : DyadicInterval 40),(⟨-193309446464,-193309446400⟩ : DyadicInterval 40),(⟨747770574647,747770593976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28958516096,-28917152192⟩ : DyadicInterval 40),(⟨776581959712,776602660928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2376_ok : ecellOkT e2376 = true := by decide +kernel
theorem e2376_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2376 e2376_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '999/1000', '7993/8000']  interval_lower 231749249/1099511627776
noncomputable def e2377 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276681667322,0,true,164265011712,164265011776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922341588230,0,false,-193190508992,-193190508928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276817686891,0,true,164382149056,164382149120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922205568661,0,false,-193352668160,-193352668096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590706071,0,true,79075392,79075456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432549481,0,false,-79081152,-79081088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602064051,0,true,90432512,90432576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421191501,0,false,-90440000,-90439936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620337,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622089,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276770337205,0,true,164341373888,164341373952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922252918347,0,false,-193296216320,-193296216256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276895335335,0,true,164449012800,164449012864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922127920217,0,false,-193445249408,-193445249344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070894395440,0,false,-28996236608,-28996236544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070934713013,0,false,-28954842432,-28954842368⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164265011712,164265011776⟩ : DyadicInterval 40),(⟨-193190508992,-193190508928⟩ : DyadicInterval 40),(⟨747786796587,747786815916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164382149056,164382149120⟩ : DyadicInterval 40),(⟨-193352668160,-193352668096⟩ : DyadicInterval 40),(⟨747764677725,747764697054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79078295,90436275⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79075392,79075456⟩ : DyadicInterval 40),(⟨-79081152,-79081088⟩ : DyadicInterval 40),(⟨762123380744,762123400073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90432512,90432576⟩ : DyadicInterval 40),(⟨-90440000,-90439936⟩ : DyadicInterval 40),(⟨762123379857,762123399186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177258709429,177383707559⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164341373888,164341373952⟩ : DyadicInterval 40),(⟨-193296216320,-193296216256⟩ : DyadicInterval 40),(⟨747772379455,747772398784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164449012800,164449012864⟩ : DyadicInterval 40),(⟨-193445249408,-193445249344⟩ : DyadicInterval 40),(⟨747752043115,747752062445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28996236608,-28954842368⟩ : DyadicInterval 40),(⟨776600804800,776621521184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2377_ok : ecellOkT e2377 = true := by decide +kernel
theorem e2377_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2377 e2377_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '7993/8000', '3997/4000']  interval_lower 115173693/549755813888
noncomputable def e2378 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276589984601,0,true,164186049280,164186049344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922433270951,0,false,-193081220672,-193081220608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276726004170,0,true,164303195072,164303195136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922297251382,0,false,-193243363712,-193243363648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579364069,0,true,67734144,67734208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443891483,0,false,-67738432,-67738368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590706968,0,true,79076288,79076352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432548584,0,false,-79082048,-79081984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622088,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623604,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276667520219,0,true,164252827776,164252827840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922355735333,0,false,-193173644544,-193173644480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276792518376,0,true,164360475392,164360475456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922230737176,0,false,-193322661120,-193322661056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070927560652,0,false,-28962185664,-28962185600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070967854855,0,false,-28920816768,-28920816704⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164186049280,164186049344⟩ : DyadicInterval 40),(⟨-193081220672,-193081220608⟩ : DyadicInterval 40),(⟨747801695911,747801715241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164303195072,164303195136⟩ : DyadicInterval 40),(⟨-193243363712,-193243363648⟩ : DyadicInterval 40),(⟨747779588670,747779607999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67736293,79079192⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67734144,67734208⟩ : DyadicInterval 40),(⟨-67738432,-67738368⟩ : DyadicInterval 40),(⟨762123381522,762123400852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79076288,79076352⟩ : DyadicInterval 40),(⟨-79082048,-79081984⟩ : DyadicInterval 40),(⟨762123380744,762123400073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177155892443,177280890600⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164252827776,164252827840⟩ : DyadicInterval 40),(⟨-193173644544,-193173644480⟩ : DyadicInterval 40),(⟨747789096142,747789115471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164360475392,164360475456⟩ : DyadicInterval 40),(⟨-193322661120,-193322661056⟩ : DyadicInterval 40),(⟨747768771821,747768791150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28962185664,-28920816704⟩ : DyadicInterval 40),(⟨776583791968,776604495712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2378_ok : ecellOkT e2378 = true := by decide +kernel
theorem e2378_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2378 e2378_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '7993/8000', '3997/4000']  interval_lower 28946711/137438953472
noncomputable def e2379 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276703835745,0,true,164284103552,164284103616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922319419807,0,false,-193216936064,-193216936000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276839869558,0,true,164401251136,164401251200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922183385994,0,false,-193379116032,-193379115968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579409299,0,true,67779392,67779456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443846253,0,false,-67783616,-67783552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590759740,0,true,79129088,79129152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432495812,0,false,-79134848,-79134784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622080,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623598,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276781421216,0,true,164350918976,164350919040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922241834336,0,false,-193309430784,-193309430720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276906426499,0,true,164458563136,164458563200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922116829053,0,false,-193458474240,-193458474176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070890816664,0,false,-28999911040,-28999910976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070931139065,0,false,-28958511744,-28958511680⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164284103552,164284103616⟩ : DyadicInterval 40),(⟨-193216936064,-193216936000⟩ : DyadicInterval 40),(⟨747783192874,747783212203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164401251136,164401251200⟩ : DyadicInterval 40),(⟨-193379116032,-193379115968⟩ : DyadicInterval 40),(⟨747761068840,747761088170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67781523,79131964⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67779392,67779456⟩ : DyadicInterval 40),(⟨-67783616,-67783552⟩ : DyadicInterval 40),(⟨762123381485,762123400814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79129088,79129152⟩ : DyadicInterval 40),(⟨-79134848,-79134784⟩ : DyadicInterval 40),(⟨762123380736,762123400066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177269793440,177394798723⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164350918976,164350919040⟩ : DyadicInterval 40),(⟨-193309430784,-193309430720⟩ : DyadicInterval 40),(⟨747770576782,747770596112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164458563136,164458563200⟩ : DyadicInterval 40),(⟨-193458474240,-193458474176⟩ : DyadicInterval 40),(⟨747750237992,747750257321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28999911040,-28958511680⟩ : DyadicInterval 40),(⟨776602639456,776623358400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2379_ok : ecellOkT e2379 = true := by decide +kernel
theorem e2379_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2379 e2379_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '999/1000', '7993/8000']  interval_lower 116489591/549755813888
noncomputable def e2380 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276795504222,0,true,164363046656,164363046720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922227751330,0,false,-193326220928,-193326220864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276931538035,0,true,164480185792,164480185856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922091717517,0,false,-193488417088,-193488417024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590758842,0,true,79128192,79128256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432496710,0,false,-79133952,-79133888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602124367,0,true,90492864,90492928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421131185,0,false,-90500352,-90500288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620327,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622081,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276884231077,0,true,164439451072,164439451136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922139024475,0,false,-193432009216,-193432009152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277009236332,0,true,164547086528,164547086592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922014019220,0,false,-193581069184,-193581069120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070857632450,0,false,-29033982656,-29033982592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070897978219,0,false,-28992558144,-28992558080⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164363046656,164363046720⟩ : DyadicInterval 40),(⟨-193326220928,-193326220864⟩ : DyadicInterval 40),(⟨747768286145,747768305475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164480185792,164480185856⟩ : DyadicInterval 40),(⟨-193488417088,-193488417024⟩ : DyadicInterval 40),(⟨747746150520,747746169849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79131066,90496591⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79128192,79128256⟩ : DyadicInterval 40),(⟨-79133952,-79133888⟩ : DyadicInterval 40),(⟨762123380736,762123400066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90492864,90492928⟩ : DyadicInterval 40),(⟨-90500352,-90500288⟩ : DyadicInterval 40),(⟨762123379847,762123399176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177372603301,177497608556⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164439451072,164439451136⟩ : DyadicInterval 40),(⟨-193432009216,-193432009152⟩ : DyadicInterval 40),(⟨747753850314,747753869644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164547086528,164547086592⟩ : DyadicInterval 40),(⟨-193581069184,-193581069120⟩ : DyadicInterval 40),(⟨747733499504,747733518834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29033982656,-28992558080⟩ : DyadicInterval 40),(⟨776619662656,776640394208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2380_ok : ecellOkT e2380 = true := by decide +kernel
theorem e2380_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2380 e2380_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '999/1000', '7993/8000']  interval_lower 117105957/549755813888
noncomputable def e2381 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276909341122,0,true,164461072832,164461072896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922113914430,0,false,-193461949568,-193461949504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277045389179,0,true,164578213824,164578213888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921977866373,0,false,-193624182720,-193624182656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590811616,0,true,79180928,79180992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432443936,0,false,-79186752,-79186688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602184686,0,true,90553152,90553216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421070866,0,false,-90560640,-90560576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620317,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622074,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276998124950,0,true,164537519488,164537519552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922025130602,0,false,-193567818880,-193567818816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277123137334,0,true,164645151488,164645151552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921900118218,0,false,-193716905792,-193716905728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070820845859,0,false,-29071754240,-29071754176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070861219829,0,false,-29030299328,-29030299264⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164461072832,164461072896⟩ : DyadicInterval 40),(⟨-193461949568,-193461949504⟩ : DyadicInterval 40),(⟨747749763599,747749782929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164578213824,164578213888⟩ : DyadicInterval 40),(⟨-193624182720,-193624182656⟩ : DyadicInterval 40),(⟨747727611164,747727630494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79183840,90556910⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79180928,79180992⟩ : DyadicInterval 40),(⟨-79186752,-79186688⟩ : DyadicInterval 40),(⟨762123380761,762123400090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90553152,90553216⟩ : DyadicInterval 40),(⟨-90560640,-90560576⟩ : DyadicInterval 40),(⟨762123379837,762123399166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177486497174,177611509558⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164537519488,164537519552⟩ : DyadicInterval 40),(⟨-193567818880,-193567818816⟩ : DyadicInterval 40),(⟨747735309070,747735328400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164645151488,164645151552⟩ : DyadicInterval 40),(⟨-193716905792,-193716905728⟩ : DyadicInterval 40),(⟨747714943811,747714963140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29071754240,-29030299264⟩ : DyadicInterval 40),(⟨776638533248,776659280000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2381_ok : ecellOkT e2381 = true := by decide +kernel
theorem e2381_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2381 e2381_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '7993/8000', '3997/4000']  interval_lower 58200799/274877906944
noncomputable def e2382 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276817686889,0,true,164382149056,164382149120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922205568663,0,false,-193352668160,-193352668096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276953734946,0,true,164499298496,164499298560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922069520606,0,false,-193514885184,-193514885120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579454531,0,true,67824640,67824704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443801021,0,false,-67828864,-67828800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590812516,0,true,79181888,79181952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432443036,0,false,-79187648,-79187584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622073,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623592,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276895322213,0,true,164449001472,164449001536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922127933339,0,false,-193445233792,-193445233728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277020334622,0,true,164556642112,164556642176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922002920930,0,false,-193594304128,-193594304064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070854049074,0,false,-29037661952,-29037661888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070894399675,0,false,-28996232256,-28996232192⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164382149056,164382149120⟩ : DyadicInterval 40),(⟨-193352668160,-193352668096⟩ : DyadicInterval 40),(⟨747764677725,747764697055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164499298496,164499298560⟩ : DyadicInterval 40),(⟨-193514885184,-193514885120⟩ : DyadicInterval 40),(⟨747742536910,747742556240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67826755,79184740⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67824640,67824704⟩ : DyadicInterval 40),(⟨-67828864,-67828800⟩ : DyadicInterval 40),(⟨762123381479,762123400809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79181888,79181952⟩ : DyadicInterval 40),(⟨-79187648,-79187584⟩ : DyadicInterval 40),(⟨762123380729,762123400058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177383694437,177508706846⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164449001472,164449001536⟩ : DyadicInterval 40),(⟨-193445233792,-193445233728⟩ : DyadicInterval 40),(⟨747752045280,747752064610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164556642112,164556642176⟩ : DyadicInterval 40),(⟨-193594304128,-193594304064⟩ : DyadicInterval 40),(⟨747731692053,747731711382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29037661952,-28996232192⟩ : DyadicInterval 40),(⟨776621499712,776642233856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2382_ok : ecellOkT e2382 = true := by decide +kernel
theorem e2382_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2382 e2382_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '7993/8000', '3997/4000']  interval_lower 234035609/1099511627776
noncomputable def e2383 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276931538033,0,true,164480185792,164480185856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922091717519,0,false,-193488417088,-193488417024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277067600334,0,true,164597337088,164597337152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921955655218,0,false,-193650671104,-193650671040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579499767,0,true,67869888,67869952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443755785,0,false,-67874112,-67874048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590865296,0,true,79234624,79234688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432390256,0,false,-79240384,-79240320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622065,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623587,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277009223207,0,true,164547075200,164547075264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922014032345,0,false,-193581053568,-193581053504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277134242745,0,true,164654712384,164654712448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921889012807,0,false,-193730150784,-193730150720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070817257883,0,false,-29075438400,-29075438336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070857636688,0,false,-29033978304,-29033978240⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164480185792,164480185856⟩ : DyadicInterval 40),(⟨-193488417088,-193488417024⟩ : DyadicInterval 40),(⟨747746150520,747746169850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164597337088,164597337152⟩ : DyadicInterval 40),(⟨-193650671104,-193650671040⟩ : DyadicInterval 40),(⟨747723992887,747724012217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67871991,79237520⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67869888,67869952⟩ : DyadicInterval 40),(⟨-67874112,-67874048⟩ : DyadicInterval 40),(⟨762123381474,762123400803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79234624,79234688⟩ : DyadicInterval 40),(⟨-79240384,-79240320⟩ : DyadicInterval 40),(⟨762123380721,762123400050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177497595431,177622614969⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164547075200,164547075264⟩ : DyadicInterval 40),(⟨-193581053568,-193581053504⟩ : DyadicInterval 40),(⟨747733501672,747733521002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164654712384,164654712448⟩ : DyadicInterval 40),(⟨-193730150784,-193730150720⟩ : DyadicInterval 40),(⟨747713133965,747713153295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29075438400,-29033978240⟩ : DyadicInterval 40),(⟨776640372736,776661122080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2383_ok : ecellOkT e2383 = true := by decide +kernel
theorem e2383_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2383 e2383_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '3997/4000', '1599/1600']  interval_lower 230172305/1099511627776
noncomputable def e2384 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276612138780,0,true,164205130240,164205130304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922411116772,0,false,-193107628032,-193107627968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276748172594,0,true,164322286272,164322286336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922275082958,0,false,-193269791936,-193269791872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568074779,0,true,56445504,56445568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455180773,0,false,-56448512,-56448448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579410142,0,true,67780224,67780288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443845410,0,false,-67784512,-67784448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623597,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624879,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276678597141,0,true,164262367552,164262367616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922344658411,0,false,-193186849088,-193186849024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276803602447,0,true,164370020416,164370020480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922219653105,0,false,-193335875904,-193335875840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070923986237,0,false,-28965855488,-28965855424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070964285265,0,false,-28924481536,-28924481472⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164205130240,164205130304⟩ : DyadicInterval 40),(⟨-193107628032,-193107627968⟩ : DyadicInterval 40),(⟨747798096356,747798115686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164322286272,164322286336⟩ : DyadicInterval 40),(⟨-193269791936,-193269791872⟩ : DyadicInterval 40),(⟨747775983976,747776003305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56447003,67782366⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56445504,56445568⟩ : DyadicInterval 40),(⟨-56448512,-56448448⟩ : DyadicInterval 40),(⟨762123382158,762123401487⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67780224,67780288⟩ : DyadicInterval 40),(⟨-67784512,-67784448⟩ : DyadicInterval 40),(⟨762123381517,762123400846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177166969365,177291974671⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164262367552,164262367616⟩ : DyadicInterval 40),(⟨-193186849088,-193186849024⟩ : DyadicInterval 40),(⟨747787295673,747787315002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164370020416,164370020480⟩ : DyadicInterval 40),(⟨-193335875904,-193335875840⟩ : DyadicInterval 40),(⟨747766968851,747766988180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28965855488,-28924481472⟩ : DyadicInterval 40),(⟨776585624352,776606330624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2384_ok : ecellOkT e2384 = true := by decide +kernel
theorem e2384_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2384 e2384_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '3997/4000', '1599/1600']  interval_lower 231398245/1099511627776
noncomputable def e2385 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276726004168,0,true,164303195072,164303195136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922297251384,0,false,-193243363648,-193243363584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276862052225,0,true,164420352896,164420352960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922161203327,0,false,-193405564608,-193405564544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568112471,0,true,56483200,56483264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455143081,0,false,-56486208,-56486144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579455374,0,true,67825472,67825536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443800178,0,false,-67829696,-67829632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623591,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624875,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276792505259,0,true,164360464064,164360464128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922230750293,0,false,-193322645440,-193322645376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276917517685,0,true,164468113408,164468113472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922105737867,0,false,-193471699200,-193471699136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070887237656,0,false,-29003585728,-29003585664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070927564882,0,false,-28962181312,-28962181248⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164303195072,164303195136⟩ : DyadicInterval 40),(⟨-193243363648,-193243363584⟩ : DyadicInterval 40),(⟨747779588643,747779607973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164420352896,164420352960⟩ : DyadicInterval 40),(⟨-193405564608,-193405564544⟩ : DyadicInterval 40),(⟨747757459518,747757478847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56484695,67827598⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56483200,56483264⟩ : DyadicInterval 40),(⟨-56486208,-56486144⟩ : DyadicInterval 40),(⟨762123382154,762123401483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67825472,67825536⟩ : DyadicInterval 40),(⟨-67829696,-67829632⟩ : DyadicInterval 40),(⟨762123381479,762123400808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177280877483,177405889909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164360464064,164360464128⟩ : DyadicInterval 40),(⟨-193322645440,-193322645376⟩ : DyadicInterval 40),(⟨747768773956,747768793285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164468113408,164468113472⟩ : DyadicInterval 40),(⟨-193471699200,-193471699136⟩ : DyadicInterval 40),(⟨747748432725,747748452055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29003585728,-28962181248⟩ : DyadicInterval 40),(⟨776604474240,776625195744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2385_ok : ecellOkT e2385 = true := by decide +kernel
theorem e2385_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2385 e2385_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '1599/1600', '1999/2000']  interval_lower 114998495/549755813888
noncomputable def e2386 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276634292960,0,true,164224210880,164224210944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922388962592,0,false,-193134036096,-193134036032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276770341017,0,true,164341377152,164341377216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922252914535,0,false,-193296220864,-193296220800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556785436,0,true,45156672,45156736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466470116,0,false,-45158592,-45158528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568113259,0,true,56484032,56484096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455142293,0,false,-56486976,-56486912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624874,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625922,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276689674086,0,true,164271907328,164271907392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922333581466,0,false,-193200053824,-193200053760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276814686542,0,true,164379565376,164379565440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922208569010,0,false,-193349090944,-193349090880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070920411590,0,false,-28969525568,-28969525504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070960715443,0,false,-28928146496,-28928146432⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164224210880,164224210944⟩ : DyadicInterval 40),(⟨-193134036096,-193134036032⟩ : DyadicInterval 40),(⟨747794496365,747794515695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164341377152,164341377216⟩ : DyadicInterval 40),(⟨-193296220864,-193296220800⟩ : DyadicInterval 40),(⟨747772378845,747772398175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45157660,56485483⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45156672,45156736⟩ : DyadicInterval 40),(⟨-45158592,-45158528⟩ : DyadicInterval 40),(⟨762123382657,762123401986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56484032,56484096⟩ : DyadicInterval 40),(⟨-56486976,-56486912⟩ : DyadicInterval 40),(⟨762123382122,762123401451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177178046310,177303058766⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164271907328,164271907392⟩ : DyadicInterval 40),(⟨-193200053824,-193200053760⟩ : DyadicInterval 40),(⟨747785495052,747785514382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164379565376,164379565440⟩ : DyadicInterval 40),(⟨-193349090944,-193349090880⟩ : DyadicInterval 40),(⟨747765165792,747765185122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28969525568,-28928146432⟩ : DyadicInterval 40),(⟨776587456832,776608165664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2386_ok : ecellOkT e2386 = true := by decide +kernel
theorem e2386_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2386 e2386_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '1599/1600', '1999/2000']  interval_lower 231222815/1099511627776
noncomputable def e2387 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276748172592,0,true,164322286272,164322286336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922275082960,0,false,-193269791936,-193269791872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276884234893,0,true,164439454336,164439454400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922139020659,0,false,-193432013760,-193432013696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556815589,0,true,45186880,45186944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466439963,0,false,-45188800,-45188736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568150955,0,true,56521664,56521728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455104597,0,false,-56524672,-56524608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624870,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625919,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276803589326,0,true,164370009088,164370009152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922219666226,0,false,-193335860288,-193335860224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276928608903,0,true,164477663680,164477663744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922094646649,0,false,-193484924352,-193484924288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070883658414,0,false,-29007260672,-29007260608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070923990469,0,false,-28965851136,-28965851072⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164322286272,164322286336⟩ : DyadicInterval 40),(⟨-193269791936,-193269791872⟩ : DyadicInterval 40),(⟨747775983976,747776003306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164439454336,164439454400⟩ : DyadicInterval 40),(⟨-193432013760,-193432013696⟩ : DyadicInterval 40),(⟨747753849703,747753869033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45187813,56523179⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45186880,45186944⟩ : DyadicInterval 40),(⟨-45188800,-45188736⟩ : DyadicInterval 40),(⟨762123382654,762123401983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56521664,56521728⟩ : DyadicInterval 40),(⟨-56524672,-56524608⟩ : DyadicInterval 40),(⟨762123382150,762123401479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177291961550,177416981127⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164370009088,164370009152⟩ : DyadicInterval 40),(⟨-193335860288,-193335860224⟩ : DyadicInterval 40),(⟨747766971014,747766990343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164477663680,164477663744⟩ : DyadicInterval 40),(⟨-193484924352,-193484924288⟩ : DyadicInterval 40),(⟨747746627305,747746646634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29007260672,-28965851072⟩ : DyadicInterval 40),(⟨776606309152,776627033216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2387_ok : ecellOkT e2387 = true := by decide +kernel
theorem e2387_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2387 e2387_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '3997/4000', '1599/1600']  interval_lower 232627337/1099511627776
noncomputable def e2388 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276839869556,0,true,164401251136,164401251200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922183385996,0,false,-193379116032,-193379115968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276975931857,0,true,164518410816,164518410880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922047323695,0,false,-193541353984,-193541353920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568150165,0,true,56520896,56520960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455105387,0,false,-56523904,-56523840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579500612,0,true,67870720,67870784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443754940,0,false,-67874944,-67874880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623586,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624871,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276906413376,0,true,164458551808,164458551872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922116842176,0,false,-193458458560,-193458458496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277031432933,0,true,164566197696,164566197760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921991822619,0,false,-193607539200,-193607539136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070850465468,0,false,-29041341440,-29041341376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070890820899,0,false,-28999906688,-28999906624⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164401251136,164401251200⟩ : DyadicInterval 40),(⟨-193379116032,-193379115968⟩ : DyadicInterval 40),(⟨747761068841,747761088170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164518410816,164518410880⟩ : DyadicInterval 40),(⟨-193541353984,-193541353920⟩ : DyadicInterval 40),(⟨747738922898,747738942228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56522389,67872836⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56520896,56520960⟩ : DyadicInterval 40),(⟨-56523904,-56523840⟩ : DyadicInterval 40),(⟨762123382150,762123401479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67870720,67870784⟩ : DyadicInterval 40),(⟨-67874944,-67874880⟩ : DyadicInterval 40),(⟨762123381474,762123400803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177394785600,177519805157⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164458551808,164458551872⟩ : DyadicInterval 40),(⟨-193458458560,-193458458496⟩ : DyadicInterval 40),(⟨747750240130,747750259460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164566197696,164566197760⟩ : DyadicInterval 40),(⟨-193607539200,-193607539136⟩ : DyadicInterval 40),(⟨747729884421,747729903750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29041341440,-28999906624⟩ : DyadicInterval 40),(⟨776623336928,776644073600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2388_ok : ecellOkT e2388 = true := by decide +kernel
theorem e2388_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2388 e2388_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '3997/4000', '1599/1600']  interval_lower 233859503/1099511627776
noncomputable def e2389 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276953734944,0,true,164499298496,164499298560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922069520608,0,false,-193514885184,-193514885120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277089811489,0,true,164616459968,164616460032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921933444063,0,false,-193677160128,-193677160064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568187862,0,true,56558592,56558656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455067690,0,false,-56561600,-56561536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579545851,0,true,67915968,67916032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443709701,0,false,-67920192,-67920128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623580,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624867,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277020321496,0,true,164556630848,164556630912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922002934056,0,false,-193594288448,-193594288384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277145348178,0,true,164664273280,164664273344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921877907374,0,false,-193743396032,-193743395968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070813669676,0,false,-29079122752,-29079122688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070854053313,0,false,-29037657600,-29037657536⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164499298496,164499298560⟩ : DyadicInterval 40),(⟨-193514885184,-193514885120⟩ : DyadicInterval 40),(⟨747742536910,747742556240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164616459968,164616460032⟩ : DyadicInterval 40),(⟨-193677160128,-193677160064⟩ : DyadicInterval 40),(⟨747720374181,747720393511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56560086,67918075⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56558592,56558656⟩ : DyadicInterval 40),(⟨-56561600,-56561536⟩ : DyadicInterval 40),(⟨762123382146,762123401475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67915968,67916032⟩ : DyadicInterval 40),(⟨-67920192,-67920128⟩ : DyadicInterval 40),(⟨762123381468,762123400797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177508693720,177633720402⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164556630848,164556630912⟩ : DyadicInterval 40),(⟨-193594288448,-193594288384⟩ : DyadicInterval 40),(⟨747731694157,747731713487⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164664273280,164664273344⟩ : DyadicInterval 40),(⟨-193743396032,-193743395968⟩ : DyadicInterval 40),(⟨747711323993,747711343322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29079122752,-29037657536⟩ : DyadicInterval 40),(⟨776642212384,776662964256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2389_ok : ecellOkT e2389 = true := by decide +kernel
theorem e2389_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2389 e2389_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '1599/1600', '1999/2000']  interval_lower 58112909/274877906944
noncomputable def e2390 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276862052223,0,true,164420352896,164420352960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922161203329,0,false,-193405564608,-193405564544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276998128768,0,true,164537522816,164537522880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922025126784,0,false,-193567823424,-193567823360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556845745,0,true,45217024,45217088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466409807,0,false,-45218944,-45218880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568188652,0,true,56559360,56559424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455066900,0,false,-56562368,-56562304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624866,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625917,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276917504563,0,true,164468102144,164468102208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922105750989,0,false,-193471683520,-193471683456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277042531269,0,true,164575753216,164575753280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921980724283,0,false,-193620774528,-193620774464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070846881629,0,false,-29045021248,-29045021184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070887241891,0,false,-29003581376,-29003581312⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164420352896,164420352960⟩ : DyadicInterval 40),(⟨-193405564608,-193405564544⟩ : DyadicInterval 40),(⟨747757459518,747757478847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164537522816,164537522880⟩ : DyadicInterval 40),(⟨-193567823424,-193567823360⟩ : DyadicInterval 40),(⟨747735308421,747735327750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45217969,56560876⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45217024,45217088⟩ : DyadicInterval 40),(⟨-45218944,-45218880⟩ : DyadicInterval 40),(⟨762123382652,762123401981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56559360,56559424⟩ : DyadicInterval 40),(⟨-56562368,-56562304⟩ : DyadicInterval 40),(⟨762123382146,762123401475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177405876787,177530903493⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164468102144,164468102208⟩ : DyadicInterval 40),(⟨-193471683520,-193471683456⟩ : DyadicInterval 40),(⟨747748434827,747748454156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164575753216,164575753280⟩ : DyadicInterval 40),(⟨-193620774528,-193620774464⟩ : DyadicInterval 40),(⟨747728076700,747728096029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29045021248,-29003581312⟩ : DyadicInterval 40),(⟨776625174272,776645913504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2390_ok : ecellOkT e2390 = true := by decide +kernel
theorem e2390_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2390 e2390_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '1599/1600', '1999/2000']  interval_lower 233683217/1099511627776
noncomputable def e2391 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276975931855,0,true,164518410816,164518410880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922047323697,0,false,-193541353984,-193541353920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277112022644,0,true,164635582464,164635582528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921911232908,0,false,-193703649856,-193703649792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556875903,0,true,45247168,45247232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466379649,0,false,-45249088,-45249024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568226352,0,true,56597056,56597120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455029200,0,false,-56600064,-56600000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624862,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625914,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277031419806,0,true,164566186432,164566186496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921991835746,0,false,-193607523584,-193607523520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277156453631,0,true,164673834048,164673834112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921866801921,0,false,-193756641472,-193756641408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070810081238,0,false,-29082807360,-29082807296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070850469708,0,false,-29041337088,-29041337024⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164518410816,164518410880⟩ : DyadicInterval 40),(⟨-193541353984,-193541353920⟩ : DyadicInterval 40),(⟨747738922899,747738942228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164635582464,164635582528⟩ : DyadicInterval 40),(⟨-193703649856,-193703649792⟩ : DyadicInterval 40),(⟨747716755071,747716774400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45248127,56598576⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45247168,45247232⟩ : DyadicInterval 40),(⟨-45249088,-45249024⟩ : DyadicInterval 40),(⟨762123382649,762123401978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56597056,56597120⟩ : DyadicInterval 40),(⟨-56600064,-56600000⟩ : DyadicInterval 40),(⟨762123382142,762123401471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177519792030,177644825855⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164566186432,164566186496⟩ : DyadicInterval 40),(⟨-193607523584,-193607523520⟩ : DyadicInterval 40),(⟨747729886553,747729905883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164673834048,164673834112⟩ : DyadicInterval 40),(⟨-193756641472,-193756641408⟩ : DyadicInterval 40),(⟨747709513942,747709533271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29082807360,-29041337024⟩ : DyadicInterval 40),(⟨776644052128,776664806560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2391_ok : ecellOkT e2391 = true := by decide +kernel
theorem e2391_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2391 e2391_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '1999/2000', '7997/8000']  interval_lower 224949571/1099511627776
noncomputable def e2392 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276200871636,0,true,163850859904,163850859968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922822383916,0,false,-192617507968,-192617507904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276336876962,0,true,163968029120,163968029184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922686378590,0,false,-192779565632,-192779565568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545405595,0,true,33777280,33777344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477849957,0,false,-33778368,-33778304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556695721,0,true,45067008,45067072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466559831,0,false,-45068928,-45068864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625928,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626739,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276245061615,0,true,163888931136,163888931200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922778193937,0,false,-192670160064,-192670160000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276370052718,0,true,163996608256,163996608320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922653202834,0,false,-192819099968,-192819099904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071063631699,0,false,-28822491648,-28822491584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071103827579,0,false,-28781228928,-28781228864⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163850859904,163850859968⟩ : DyadicInterval 40),(⟨-192617507968,-192617507904⟩ : DyadicInterval 40),(⟨747864842964,747864862294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163968029120,163968029184⟩ : DyadicInterval 40),(⟨-192779565632,-192779565568⟩ : DyadicInterval 40),(⟨747842787450,747842806779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33777819,45067945⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33777280,33777344⟩ : DyadicInterval 40),(⟨-33778368,-33778304⟩ : DyadicInterval 40),(⟨762123383058,762123402387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45067008,45067072⟩ : DyadicInterval 40),(⟨-45068928,-45068864⟩ : DyadicInterval 40),(⟨762123382664,762123401993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176733433839,176858424942⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163888931136,163888931200⟩ : DyadicInterval 40),(⟨-192670160064,-192670160000⟩ : DyadicInterval 40),(⟨747857678718,747857698047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163996608256,163996608320⟩ : DyadicInterval 40),(⟨-192819099968,-192819099904⟩ : DyadicInterval 40),(⟨747837404859,747837424189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28822491648,-28781228864⟩ : DyadicInterval 40),(⟨776513998048,776534648704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2392_ok : ecellOkT e2392 = true := by decide +kernel
theorem e2392_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2392 e2392_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '1999/2000', '7997/8000']  interval_lower 56540823/274877906944
noncomputable def e2393 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276314765512,0,true,163948980864,163948980928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922708490040,0,false,-192753217024,-192753216960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276450785082,0,true,164066151872,164066151936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922572470470,0,false,-192915311680,-192915311616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545428203,0,true,33799872,33799936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477827349,0,false,-33800960,-33800896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556725869,0,true,45097152,45097216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466529683,0,false,-45099072,-45099008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625926,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626737,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276358983976,0,true,163987073216,163987073280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922664271576,0,false,-192805909568,-192805909504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276483982203,0,true,164094746944,164094747008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922539273349,0,false,-192954876352,-192954876288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071026968368,0,false,-28860129408,-28860129344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071067192443,0,false,-28818836352,-28818836288⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163948980864,163948980928⟩ : DyadicInterval 40),(⟨-192753217024,-192753216960⟩ : DyadicInterval 40),(⟨747846374357,747846393687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164066151872,164066151936⟩ : DyadicInterval 40),(⟨-192915311680,-192915311616⟩ : DyadicInterval 40),(⟨747824302086,747824321416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33800427,45098093⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33799872,33799936⟩ : DyadicInterval 40),(⟨-33800960,-33800896⟩ : DyadicInterval 40),(⟨762123383056,762123402385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45097152,45097216⟩ : DyadicInterval 40),(⟨-45099072,-45099008⟩ : DyadicInterval 40),(⟨762123382662,762123401991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176847356200,176972354427⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163987073216,163987073280⟩ : DyadicInterval 40),(⟨-192805909568,-192805909504⟩ : DyadicInterval 40),(⟨747839200804,747839220133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164094746944,164094747008⟩ : DyadicInterval 40),(⟨-192954876352,-192954876288⟩ : DyadicInterval 40),(⟨747818912446,747818931776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28860129408,-28818836288⟩ : DyadicInterval 40),(⟨776532801760,776553467584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2393_ok : ecellOkT e2393 = true := by decide +kernel
theorem e2393_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2393 e2393_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '7997/8000', '3999/4000']  interval_lower 224775583/1099511627776
noncomputable def e2394 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276222968840,0,true,163869897600,163869897664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922800286712,0,false,-192643836352,-192643836288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276358988410,0,true,163987077056,163987077120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922664267142,0,false,-192805914880,-192805914816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534146290,0,true,22518272,22518336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489109262,0,false,-22518784,-22518720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545428880,0,true,33800576,33800640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477826672,0,false,-33801664,-33801600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626736,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627315,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276256110126,0,true,163898449600,163898449664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922767145426,0,false,-192683324736,-192683324672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276381108377,0,true,164006131968,164006132032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922642147175,0,false,-192832274880,-192832274816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071060074943,0,false,-28826142912,-28826142848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071100275634,0,false,-28784875072,-28784875008⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163869897600,163869897664⟩ : DyadicInterval 40),(⟨-192643836352,-192643836288⟩ : DyadicInterval 40),(⟨747861260711,747861280040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163987077056,163987077120⟩ : DyadicInterval 40),(⟨-192805914880,-192805914816⟩ : DyadicInterval 40),(⟨747839200085,747839219414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22518514,33801104⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22518272,22518336⟩ : DyadicInterval 40),(⟨-22518784,-22518720⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33800576,33800640⟩ : DyadicInterval 40),(⟨-33801664,-33801600⟩ : DyadicInterval 40),(⟨762123383056,762123402385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176744482350,176869480601⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163898449600,163898449664⟩ : DyadicInterval 40),(⟨-192683324736,-192683324672⟩ : DyadicInterval 40),(⟨747855887232,747855906562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164006131968,164006132032⟩ : DyadicInterval 40),(⟨-192832274880,-192832274816⟩ : DyadicInterval 40),(⟨747835610885,747835630215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28826142912,-28784875008⟩ : DyadicInterval 40),(⟨776515821120,776536474336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2394_ok : ecellOkT e2394 = true := by decide +kernel
theorem e2394_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2394 e2394_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '7997/8000', '3999/4000']  interval_lower 28248615/137438953472
noncomputable def e2395 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276336876960,0,true,163968029120,163968029184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922686378592,0,false,-192779565632,-192779565568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276472910774,0,true,164085210368,164085210432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922550344778,0,false,-192941681152,-192941681088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534161361,0,true,22533312,22533376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489094191,0,false,-22533824,-22533760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545451491,0,true,33823168,33823232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477804061,0,false,-33824256,-33824192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626735,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627315,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276370039608,0,true,163996596992,163996597056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922653215944,0,false,-192819084352,-192819084288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276495044982,0,true,164104275904,164104275968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922528210570,0,false,-192968061440,-192968061376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071023407029,0,false,-28863785472,-28863785408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071063635918,0,false,-28822487296,-28822487232⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163968029120,163968029184⟩ : DyadicInterval 40),(⟨-192779565632,-192779565568⟩ : DyadicInterval 40),(⟨747842787450,747842806780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164085210368,164085210432⟩ : DyadicInterval 40),(⟨-192941681152,-192941681088⟩ : DyadicInterval 40),(⟨747820710060,747820729389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22533585,33823715⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22533312,22533376⟩ : DyadicInterval 40),(⟨-22533824,-22533760⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33823168,33823232⟩ : DyadicInterval 40),(⟨-33824256,-33824192⟩ : DyadicInterval 40),(⟨762123383055,762123402384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176858411832,176983417206⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163996596992,163996597056⟩ : DyadicInterval 40),(⟨-192819084352,-192819084288⟩ : DyadicInterval 40),(⟨747837406972,747837426302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164104275904,164104275968⟩ : DyadicInterval 40),(⟨-192968061440,-192968061376⟩ : DyadicInterval 40),(⟨747817116187,747817135516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28863785472,-28822487232⟩ : DyadicInterval 40),(⟨776534627232,776555295616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2395_ok : ecellOkT e2395 = true := by decide +kernel
theorem e2395_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2395 e2395_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '1999/2000', '7997/8000']  interval_lower 3552809/17179869184
noncomputable def e2396 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276428659388,0,true,164047093056,164047093120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922594596164,0,false,-192888942848,-192888942784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276564693202,0,true,164164265920,164164265984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922458562350,0,false,-193051074496,-193051074432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545450813,0,true,33822464,33822528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477804739,0,false,-33823616,-33823552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556756018,0,true,45127296,45127360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466499534,0,false,-45129216,-45129152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625923,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626736,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276472906336,0,true,164085206592,164085206656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922550349216,0,false,-192941675904,-192941675840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276597911692,0,true,164192876800,164192876864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922425343860,0,false,-193090669568,-193090669504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070990281426,0,false,-28897792704,-28897792640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071030533699,0,false,-28856469248,-28856469184⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164047093056,164047093120⟩ : DyadicInterval 40),(⟨-192888942848,-192888942784⟩ : DyadicInterval 40),(⟨747827893654,747827912983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164164265920,164164265984⟩ : DyadicInterval 40),(⟨-193051074496,-193051074432⟩ : DyadicInterval 40),(⟨747805804581,747805823910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33823037,45128242⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33822464,33822528⟩ : DyadicInterval 40),(⟨-33823616,-33823552⟩ : DyadicInterval 40),(⟨762123383087,762123402416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45127296,45127360⟩ : DyadicInterval 40),(⟨-45129216,-45129152⟩ : DyadicInterval 40),(⟨762123382659,762123401988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176961278560,177086283916⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164085206592,164085206656⟩ : DyadicInterval 40),(⟨-192941675904,-192941675840⟩ : DyadicInterval 40),(⟨747820710771,747820730100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164192876800,164192876864⟩ : DyadicInterval 40),(⟨-193090669568,-193090669504⟩ : DyadicInterval 40),(⟨747800407982,747800427311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28897792704,-28856469184⟩ : DyadicInterval 40),(⟨776551618208,776572299232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2396_ok : ecellOkT e2396 = true := by decide +kernel
theorem e2396_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2396 e2396_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '1999/2000', '7997/8000']  interval_lower 57149833/274877906944
noncomputable def e2397 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276542553264,0,true,164145196480,164145196544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922480702288,0,false,-193024685440,-193024685376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276678601321,0,true,164262371136,164262371200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922344654231,0,false,-193186854080,-193186854016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545473425,0,true,33845120,33845184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477782127,0,false,-33846208,-33846144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556786170,0,true,45157440,45157504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466469382,0,false,-45159360,-45159296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625921,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626735,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276586828697,0,true,164183331136,164183331200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922436426855,0,false,-193077458944,-193077458880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276711841173,0,true,164290997888,164290997952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922311414379,0,false,-193226479488,-193226479424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070953570876,0,false,-28935481536,-28935481472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070993851348,0,false,-28894127744,-28894127680⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164145196480,164145196544⟩ : DyadicInterval 40),(⟨-193024685440,-193024685376⟩ : DyadicInterval 40),(⟨747809400851,747809420181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164262371136,164262371200⟩ : DyadicInterval 40),(⟨-193186854080,-193186854016⟩ : DyadicInterval 40),(⟨747787295007,747787314336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33845649,45158394⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33845120,33845184⟩ : DyadicInterval 40),(⟨-33846208,-33846144⟩ : DyadicInterval 40),(⟨762123383054,762123402383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45157440,45157504⟩ : DyadicInterval 40),(⟨-45159360,-45159296⟩ : DyadicInterval 40),(⟨762123382657,762123401986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177075200921,177200213397⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164183331136,164183331200⟩ : DyadicInterval 40),(⟨-193077458944,-193077458880⟩ : DyadicInterval 40),(⟨747802208636,747802227966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164290997888,164290997952⟩ : DyadicInterval 40),(⟨-193226479488,-193226479424⟩ : DyadicInterval 40),(⟨747781891377,747781910707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28935481536,-28894127680⟩ : DyadicInterval 40),(⟨776570447456,776591143648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2397_ok : ecellOkT e2397 = true := by decide +kernel
theorem e2397_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2397 e2397_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '7997/8000', '3999/4000']  interval_lower 113602547/549755813888
noncomputable def e2398 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276450785080,0,true,164066151872,164066151936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922572470472,0,false,-192915311680,-192915311616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276586833137,0,true,164183334976,164183335040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922436422415,0,false,-193077464192,-193077464128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534176435,0,true,22548416,22548480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489079117,0,false,-22548928,-22548864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545474103,0,true,33845760,33845824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477781449,0,false,-33846848,-33846784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626734,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627314,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276483969090,0,true,164094735616,164094735680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922539286462,0,false,-192954860736,-192954860672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276608981594,0,true,164202411072,164202411136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922414273958,0,false,-193103864704,-193103864640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070986715499,0,false,-28901453632,-28901453568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071026972591,0,false,-28860125056,-28860124992⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164066151872,164066151936⟩ : DyadicInterval 40),(⟨-192915311680,-192915311616⟩ : DyadicInterval 40),(⟨747824302087,747824321416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164183334976,164183335040⟩ : DyadicInterval 40),(⟨-193077464192,-193077464128⟩ : DyadicInterval 40),(⟨747802207887,747802227216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22548659,33846327⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22548416,22548480⟩ : DyadicInterval 40),(⟨-22548928,-22548864⟩ : DyadicInterval 40),(⟨762123383345,762123402674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33845760,33845824⟩ : DyadicInterval 40),(⟨-33846848,-33846784⟩ : DyadicInterval 40),(⟨762123383054,762123402383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176972341314,177097353818⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164094735616,164094735680⟩ : DyadicInterval 40),(⟨-192954860736,-192954860672⟩ : DyadicInterval 40),(⟨747818914600,747818933929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164202411072,164202411136⟩ : DyadicInterval 40),(⟨-193103864704,-193103864640⟩ : DyadicInterval 40),(⟨747798609343,747798628672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28901453632,-28860124992⟩ : DyadicInterval 40),(⟨776553446112,776574129696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2398_ok : ecellOkT e2398 = true := by decide +kernel
theorem e2398_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2398 e2398_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '7997/8000', '3999/4000']  interval_lower 228424265/1099511627776
noncomputable def e2399 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276564693199,0,true,164164265920,164164265984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922458562353,0,false,-193051074496,-193051074432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276700755501,0,true,164281450816,164281450880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922322500051,0,false,-193213264000,-193213263936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534191511,0,true,22563456,22563520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489064041,0,false,-22563968,-22563904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545496718,0,true,33868416,33868480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477758834,0,false,-33869504,-33869440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626732,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627313,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276597898577,0,true,164192865472,164192865536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922425356975,0,false,-193090653888,-193090653824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276722918202,0,true,164300537472,164300537536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922300337350,0,false,-193239684736,-193239684672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070950000357,0,false,-28939147264,-28939147200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070990285652,0,false,-28897788352,-28897788288⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164164265920,164164265984⟩ : DyadicInterval 40),(⟨-193051074496,-193051074432⟩ : DyadicInterval 40),(⟨747805804581,747805823911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164281450816,164281450880⟩ : DyadicInterval 40),(⟨-193213264000,-193213263936⟩ : DyadicInterval 40),(⟨747783693602,747783712931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22563735,33868942⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22563456,22563520⟩ : DyadicInterval 40),(⟨-22563968,-22563904⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33868416,33868480⟩ : DyadicInterval 40),(⟨-33869504,-33869440⟩ : DyadicInterval 40),(⟨762123383052,762123402381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177086270801,177211290426⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164192865472,164192865536⟩ : DyadicInterval 40),(⟨-193090653888,-193090653824⟩ : DyadicInterval 40),(⟨747800410112,747800429441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164300537472,164300537536⟩ : DyadicInterval 40),(⟨-193239684736,-193239684672⟩ : DyadicInterval 40),(⟨747780090381,747780109711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28939147264,-28897788288⟩ : DyadicInterval 40),(⟨776572277760,776592976512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2399_ok : ecellOkT e2399 = true := by decide +kernel
theorem e2399_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2399 e2399_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B039

end


