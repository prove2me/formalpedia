-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B021
-- name    : CK_CKLaneC2R_EpCells_B021
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:28:07.569451+00:00
-- url     : https://prove2.me/theorems/b9691e82-fea7-4b90-a5a1-db3c2cb96d38
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B021` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B021` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B021` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B021 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B021.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B021 =====
section

namespace CKLaneC2R.EpCells.B021

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['841083/4096000', '210483/1024000', '3999/4000', '1']  interval_lower 629072645/1099511627776
noncomputable def e1260 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126414,0,true,205348951296,205348951360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129138,0,false,-252716273344,-252716273280⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028117,0,true,205538011328,205538011392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227435,0,false,-253003103104,-253003103040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325231682289,0,true,205302121984,205302122048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873791573263,0,false,-252645246144,-252645246080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540773218,0,true,29145024,29145088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482482334,0,false,-29145856,-29145792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627003,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1325259898741,0,true,205325532224,205325532288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨873763356811,0,false,-252680752128,-252680752064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516036661,0,true,205538018432,205538018496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨873507218891,0,false,-253003113856,-253003113792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053056463914,0,false,-47465095424,-47465095360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053161702449,0,false,-47355219840,-47355219776⟩
    { al := (841083/4096000), au := (210483/1024000), zl := (3999/4000), zu := 1,
      A := ⟨225776498638,226004400341⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205302121984,205302122048⟩ : DyadicInterval 40),(⟨-252645246144,-252645246080⟩ : DyadicInterval 40),(⟨738788664712,738788684042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29145442⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29145024,29145088⟩ : DyadicInterval 40),(⟨-29145856,-29145792⟩ : DyadicInterval 40),(⟨762123383195,762123402524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨225748270965,226004408885⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205325532224,205325532288⟩ : DyadicInterval 40),(⟨-252680752128,-252680752064⟩ : DyadicInterval 40),(⟨738782788251,738782807581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538018432,205538018496⟩ : DyadicInterval 40),(⟨-253003113856,-253003113792⟩ : DyadicInterval 40),(⟨738729409390,738729428720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47465095424,-47355219776⟩ : DyadicInterval 40),(⟨785800993504,785855950592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨205348951296,205538011392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253003103104,-252716273280⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1260_ok : ecellOkT e1260 = true := by decide +kernel
theorem e1260_pos {a z : ℝ} (ha1 : ((841083/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((210483/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1260 e1260_ok ha1 ha2 hz1 hz2 hz

-- box ['210483/1024000', '842781/4096000', '999/1000', '3997/4000']  interval_lower 39826833/68719476736
noncomputable def e1261 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028116,0,true,205538011328,205538011392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227436,0,false,-253003103104,-253003103040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929820,0,true,205727038848,205727038912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325732,0,false,-253290007744,-253290007680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325290023715,0,true,205350525376,205350525440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873733231837,0,false,-252718660928,-252718660864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325574255594,0,true,205586309760,205586309824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873448999958,0,false,-253076398400,-253076398336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599060282,0,true,87428992,87429056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424195270,0,false,-87436032,-87435968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628331044,0,true,116697024,116697088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394924508,0,false,-116709504,-116709440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615388,0,false,-12416,-12352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620824,0,false,-6976,-6912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325403021939,0,true,205444269056,205444269120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873620233613,0,false,-252860867840,-252860867776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325659102227,0,true,205656684480,205656684544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873364153325,0,false,-253183209856,-253183209792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052997631099,0,false,-47526525376,-47526525312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053102912609,0,false,-47416598784,-47416598720⟩
    { al := (210483/1024000), au := (842781/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨226004400340,226232302044⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205350525376,205350525440⟩ : DyadicInterval 40),(⟨-252718660928,-252718660864⟩ : DyadicInterval 40),(⟨738776513455,738776532784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205586309760,205586309824⟩ : DyadicInterval 40),(⟨-253076398400,-253076398336⟩ : DyadicInterval 40),(⟨738717267997,738717287327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87432506,116703268⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87428992,87429056⟩ : DyadicInterval 40),(⟨-87436032,-87435968⟩ : DyadicInterval 40),(⟨762123380119,762123399448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116697024,116697088⟩ : DyadicInterval 40),(⟨-116709504,-116709440⟩ : DyadicInterval 40),(⟨762123377404,762123396734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12416,-6912⟩ : DyadicInterval 40),(⟨762123387072,762123409088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225891394163,226147474451⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205444269056,205444269120⟩ : DyadicInterval 40),(⟨-252860867840,-252860867776⟩ : DyadicInterval 40),(⟨738752969217,738752988547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205656684480,205656684544⟩ : DyadicInterval 40),(⟨-253183209856,-253183209792⟩ : DyadicInterval 40),(⟨738699567604,738699586933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47526525376,-47416598720⟩ : DyadicInterval 40),(⟨785831682976,785886665568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205538011328,205727038912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253290007744,-253003103040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1261_ok : ecellOkT e1261 = true := by decide +kernel
theorem e1261_pos {a z : ℝ} (ha1 : ((210483/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((842781/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1261 e1261_ok ha1 ha2 hz1 hz2 hz

-- box ['842781/4096000', '84363/409600', '999/1000', '3997/4000']  interval_lower 160628189/274877906944
noncomputable def e1262 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929819,0,true,205727038848,205727038912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325733,0,false,-253290007744,-253290007680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831522,0,true,205916033920,205916033984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424030,0,false,-253576987264,-253576987200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325517697516,0,true,205539396096,205539396160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873505558036,0,false,-253005204480,-253005204416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325801986370,0,true,205775187264,205775187328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873221269182,0,false,-253363106880,-253363106816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599154076,0,true,87522816,87522880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424101476,0,false,-87529792,-87529728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628456129,0,true,116822144,116822208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394799423,0,false,-116834624,-116834560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615362,0,false,-12416,-12352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620809,0,false,-6976,-6912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325630809688,0,true,205633218176,205633218240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873392445864,0,false,-253147591872,-253147591808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325886918476,0,true,205845620736,205845620800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873136337076,0,false,-253470053888,-253470053824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052903869435,0,false,-47624433152,-47624433088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053009268786,0,false,-47514373696,-47514373632⟩
    { al := (842781/4096000), au := (84363/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨226232302043,226460203746⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205539396096,205539396160⟩ : DyadicInterval 40),(⟨-253005204480,-253005204416⟩ : DyadicInterval 40),(⟨738729063093,738729082422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205775187264,205775187328⟩ : DyadicInterval 40),(⟨-253363106880,-253363106816⟩ : DyadicInterval 40),(⟨738669744243,738669763572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87526300,116828353⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87522816,87522880⟩ : DyadicInterval 40),(⟨-87529792,-87529728⟩ : DyadicInterval 40),(⟨762123380072,762123399401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116822144,116822208⟩ : DyadicInterval 40),(⟨-116834624,-116834560⟩ : DyadicInterval 40),(⟨762123377378,762123396707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12416,-6912⟩ : DyadicInterval 40),(⟨762123387072,762123409088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226119181912,226375290700⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205633218176,205633218240⟩ : DyadicInterval 40),(⟨-253147591872,-253147591808⟩ : DyadicInterval 40),(⟨738705470644,738705489973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205845620736,205845620800⟩ : DyadicInterval 40),(⟨-253470053888,-253470053824⟩ : DyadicInterval 40),(⟨738652007694,738652027024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47624433152,-47514373632⟩ : DyadicInterval 40),(⟨785880570432,785935619456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205727038848,205916033984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253576987264,-253290007680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1262_ok : ecellOkT e1262 = true := by decide +kernel
theorem e1262_pos {a z : ℝ} (ha1 : ((842781/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84363/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1262 e1262_ok ha1 ha2 hz1 hz2 hz

-- box ['210483/1024000', '842781/4096000', '3997/4000', '1999/2000']  interval_lower 636262013/1099511627776
noncomputable def e1263 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028116,0,true,205538011328,205538011392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227436,0,false,-253003103104,-253003103040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929820,0,true,205727038848,205727038912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325732,0,false,-253290007744,-253290007680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325346524815,0,true,205397399808,205397399872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873676730737,0,false,-252789764544,-252789764480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325630813670,0,true,205633221440,205633221504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873392441882,0,false,-253147596864,-253147596800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569916491,0,true,58287168,58287232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453339061,0,false,-58290304,-58290240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599155991,0,true,87524672,87524736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424099561,0,false,-87531712,-87531648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620808,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624686,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325431271723,0,true,205467703872,205467703936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873591983829,0,false,-252896422720,-252896422656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325687380720,0,true,205680138624,205680138688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873335874832,0,false,-253218811328,-253218811264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052985997734,0,false,-47538672704,-47538672640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053091304215,0,false,-47428718784,-47428718720⟩
    { al := (210483/1024000), au := (842781/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨226004400340,226232302044⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205397399808,205397399872⟩ : DyadicInterval 40),(⟨-252789764544,-252789764480⟩ : DyadicInterval 40),(⟨738764742454,738764761784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205633221440,205633221504⟩ : DyadicInterval 40),(⟨-253147596864,-253147596800⟩ : DyadicInterval 40),(⟨738705469828,738705489158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58288715,87528215⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58287168,58287232⟩ : DyadicInterval 40),(⟨-58290304,-58290240⟩ : DyadicInterval 40),(⟨762123382029,762123401359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87524672,87524736⟩ : DyadicInterval 40),(⟨-87531712,-87531648⟩ : DyadicInterval 40),(⟨762123380103,762123399433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225919643947,226175752944⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205467703872,205467703936⟩ : DyadicInterval 40),(⟨-252896422720,-252896422656⟩ : DyadicInterval 40),(⟨738747081239,738747100568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205680138624,205680138688⟩ : DyadicInterval 40),(⟨-253218811328,-253218811264⟩ : DyadicInterval 40),(⟨738693666747,738693686076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47538672704,-47428718720⟩ : DyadicInterval 40),(⟨785837742976,785892739232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205538011328,205727038912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253290007744,-253003103040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1263_ok : ecellOkT e1263 = true := by decide +kernel
theorem e1263_pos {a z : ℝ} (ha1 : ((210483/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((842781/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1263 e1263_ok ha1 ha2 hz1 hz2 hz

-- box ['842781/4096000', '84363/409600', '3997/4000', '1999/2000']  interval_lower 320770919/549755813888
noncomputable def e1264 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929819,0,true,205727038848,205727038912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325733,0,false,-253290007744,-253290007680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831522,0,true,205916033920,205916033984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424030,0,false,-253576987264,-253576987200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325574255592,0,true,205586309760,205586309824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873448999960,0,false,-253076398400,-253076398336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325858601421,0,true,205822138176,205822138240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873164654131,0,false,-253434395712,-253434395648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569979022,0,true,58349696,58349760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453276530,0,false,-58352832,-58352768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599249808,0,true,87618496,87618560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424005744,0,false,-87625536,-87625472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620793,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624680,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325659087957,0,true,205656672640,205656672704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873364167595,0,false,-253183191872,-253183191808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325915225456,0,true,205869094464,205869094528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873108030096,0,false,-253505700480,-253505700416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052892212621,0,false,-47636606016,-47636605952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052997636970,0,false,-47526519232,-47526519168⟩
    { al := (842781/4096000), au := (84363/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨226232302043,226460203746⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205586309760,205586309824⟩ : DyadicInterval 40),(⟨-253076398400,-253076398336⟩ : DyadicInterval 40),(⟨738717267998,738717287327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205822138176,205822138240⟩ : DyadicInterval 40),(⟨-253434395712,-253434395648⟩ : DyadicInterval 40),(⟨738657921939,738657941269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58351246,87622032⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58349696,58349760⟩ : DyadicInterval 40),(⟨-58352832,-58352768⟩ : DyadicInterval 40),(⟨762123382023,762123401352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87618496,87618560⟩ : DyadicInterval 40),(⟨-87625536,-87625472⟩ : DyadicInterval 40),(⟨762123380088,762123399418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226147460181,226403597680⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205656672640,205656672704⟩ : DyadicInterval 40),(⟨-253183191872,-253183191808⟩ : DyadicInterval 40),(⟨738699570576,738699589905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205869094464,205869094528⟩ : DyadicInterval 40),(⟨-253505700480,-253505700416⟩ : DyadicInterval 40),(⟨738646094757,738646114086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47636606016,-47526519168⟩ : DyadicInterval 40),(⟨785886643200,785941705888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205727038848,205916033984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253576987264,-253290007680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1264_ok : ecellOkT e1264 = true := by decide +kernel
theorem e1264_pos {a z : ℝ} (ha1 : ((842781/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84363/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1264 e1264_ok ha1 ha2 hz1 hz2 hz

-- box ['84363/409600', '844479/4096000', '999/1000', '3997/4000']  interval_lower 647816765/1099511627776
noncomputable def e1265 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831521,0,true,205916033920,205916033984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424031,0,false,-253576987264,-253576987200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733224,0,true,206104996480,206104996544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522328,0,false,-253864041728,-253864041664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325745371317,0,true,205728234368,205728234432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873277884235,0,false,-253291822720,-253291822656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326029717146,0,true,205964032320,205964032384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872993538406,0,false,-253649890240,-253649890176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599247888,0,true,87616576,87616640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424007664,0,false,-87623616,-87623552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628581239,0,true,116947200,116947264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394674313,0,false,-116959744,-116959680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615335,0,false,-12480,-12416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620794,0,false,-7040,-6976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325858597439,0,true,205822134848,205822134912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873164658113,0,false,-253434390720,-253434390656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326114734715,0,true,206034524544,206034524608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872908520837,0,false,-253756972736,-253756972672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052810013370,0,false,-47722448192,-47722448128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052915530581,0,false,-47612255872,-47612255808⟩
    { al := (84363/409600), au := (844479/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨226460203745,226688105448⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205728234368,205728234432⟩ : DyadicInterval 40),(⟨-253291822720,-253291822656⟩ : DyadicInterval 40),(⟨738681563510,738681582839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205964032320,205964032384⟩ : DyadicInterval 40),(⟨-253649890240,-253649890176⟩ : DyadicInterval 40),(⟨738622171278,738622190608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87620112,116953463⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87616576,87616640⟩ : DyadicInterval 40),(⟨-87623616,-87623552⟩ : DyadicInterval 40),(⟨762123380089,762123399418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116947200,116947264⟩ : DyadicInterval 40),(⟨-116959744,-116959680⟩ : DyadicInterval 40),(⟨762123377383,762123396713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12480,-6976⟩ : DyadicInterval 40),(⟨762123387104,762123409120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226346969663,226603106939⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205822134848,205822134912⟩ : DyadicInterval 40),(⟨-253434390720,-253434390656⟩ : DyadicInterval 40),(⟨738657922795,738657942125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206034524544,206034524608⟩ : DyadicInterval 40),(⟨-253756972736,-253756972672⟩ : DyadicInterval 40),(⟨738604398472,738604417802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47722448192,-47612255808⟩ : DyadicInterval 40),(⟨785929511520,785984626976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205916033920,206104996544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253864041728,-253576987200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1265_ok : ecellOkT e1265 = true := by decide +kernel
theorem e1265_pos {a z : ℝ} (ha1 : ((84363/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((844479/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1265 e1265_ok ha1 ha2 hz1 hz2 hz

-- box ['844479/4096000', '52833/256000', '999/1000', '3997/4000']  interval_lower 653141147/1099511627776
noncomputable def e1266 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733223,0,true,206104996480,206104996544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522329,0,false,-253864041728,-253864041664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634926,0,true,206293926592,206293926656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620626,0,false,-254151171072,-254151171008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325973045117,0,true,205917040256,205917040320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873050210435,0,false,-253578515648,-253578515584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326257447921,0,true,206152844928,206152844992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872765807631,0,false,-253936748352,-253936748288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599341718,0,true,87710400,87710464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423913834,0,false,-87717504,-87717440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628706373,0,true,117072320,117072384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394549179,0,false,-117084864,-117084800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615309,0,false,-12480,-12416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620779,0,false,-7040,-6976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326086385193,0,true,206011019072,206011019136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872936870359,0,false,-253721264384,-253721264320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326342550962,0,true,206223395904,206223395968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872680704590,0,false,-254043966528,-254043966464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052716062896,0,false,-47820570560,-47820570496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052821697992,0,false,-47710245312,-47710245248⟩
    { al := (844479/4096000), au := (52833/256000), zl := (999/1000), zu := (3997/4000),
      A := ⟨226688105447,226916007150⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205917040256,205917040320⟩ : DyadicInterval 40),(⟨-253578515648,-253578515584⟩ : DyadicInterval 40),(⟨738634014655,738634033984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206152844928,206152844992⟩ : DyadicInterval 40),(⟨-253936748352,-253936748288⟩ : DyadicInterval 40),(⟨738574549039,738574568369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87713942,117078597⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87710400,87710464⟩ : DyadicInterval 40),(⟨-87717504,-87717440⟩ : DyadicInterval 40),(⟨762123380106,762123399435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117072320,117072384⟩ : DyadicInterval 40),(⟨-117084864,-117084800⟩ : DyadicInterval 40),(⟨762123377356,762123396686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12480,-6976⟩ : DyadicInterval 40),(⟨762123387104,762123409120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226574757417,226830923186⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206011019072,206011019136⟩ : DyadicInterval 40),(⟨-253721264384,-253721264320⟩ : DyadicInterval 40),(⟨738610325658,738610344988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206223395904,206223395968⟩ : DyadicInterval 40),(⟨-254043966528,-254043966464⟩ : DyadicInterval 40),(⟨738556739973,738556759302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47820570560,-47710245248⟩ : DyadicInterval 40),(⟨785978506240,786033688160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206104996480,206293926656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254151171072,-253864041664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1266_ok : ecellOkT e1266 = true := by decide +kernel
theorem e1266_pos {a z : ℝ} (ha1 : ((844479/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((52833/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1266 e1266_ok ha1 ha2 hz1 hz2 hz

-- box ['84363/409600', '844479/4096000', '3997/4000', '1999/2000']  interval_lower 646842411/1099511627776
noncomputable def e1267 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831521,0,true,205916033920,205916033984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424031,0,false,-253576987264,-253576987200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733224,0,true,206104996480,206104996544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522328,0,false,-253864041728,-253864041664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325801986368,0,true,205775187264,205775187328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873221269184,0,false,-253363106880,-253363106816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326086389172,0,true,206011022336,206011022400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872936866380,0,false,-253721269440,-253721269376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570041565,0,true,58412224,58412288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453213987,0,false,-58415360,-58415296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599343642,0,true,87712320,87712384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423911910,0,false,-87719424,-87719360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620778,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624673,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325886904200,0,true,205845608896,205845608960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873136351352,0,false,-253470035904,-253470035840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326143070174,0,true,206058017856,206058017920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872880185378,0,false,-253792664576,-253792664512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052798333085,0,false,-47734646656,-47734646592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052903875315,0,false,-47624427008,-47624426944⟩
    { al := (84363/409600), au := (844479/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨226460203745,226688105448⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205775187264,205775187328⟩ : DyadicInterval 40),(⟨-253363106880,-253363106816⟩ : DyadicInterval 40),(⟨738669744243,738669763573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206011022336,206011022400⟩ : DyadicInterval 40),(⟨-253721269440,-253721269376⟩ : DyadicInterval 40),(⟨738610324865,738610344194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58413789,87715866⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58412224,58412288⟩ : DyadicInterval 40),(⟨-58415360,-58415296⟩ : DyadicInterval 40),(⟨762123382016,762123401345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87712320,87712384⟩ : DyadicInterval 40),(⟨-87719424,-87719360⟩ : DyadicInterval 40),(⟨762123380106,762123399435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226375276424,226631442398⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205845608896,205845608960⟩ : DyadicInterval 40),(⟨-253470035904,-253470035840⟩ : DyadicInterval 40),(⟨738652010674,738652030004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206058017856,206058017920⟩ : DyadicInterval 40),(⟨-253792664576,-253792664512⟩ : DyadicInterval 40),(⟨738598473480,738598492810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47734646656,-47624426944⟩ : DyadicInterval 40),(⟨785935597088,785990726208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205916033920,206104996544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253864041728,-253576987200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1267_ok : ecellOkT e1267 = true := by decide +kernel
theorem e1267_pos {a z : ℝ} (ha1 : ((84363/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((844479/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1267 e1267_ok ha1 ha2 hz1 hz2 hz

-- box ['844479/4096000', '52833/256000', '3997/4000', '1999/2000']  interval_lower 652162927/1099511627776
noncomputable def e1268 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733223,0,true,206104996480,206104996544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522329,0,false,-253864041728,-253864041664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634926,0,true,206293926592,206293926656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620626,0,false,-254151171072,-254151171008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326029717143,0,true,205964032320,205964032384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872993538409,0,false,-253649890240,-253649890176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326314176923,0,true,206199874112,206199874176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872709078629,0,false,-254008217984,-254008217920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570104121,0,true,58474752,58474816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453151431,0,false,-58477952,-58477888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599437495,0,true,87806208,87806272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423818057,0,false,-87813248,-87813184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620763,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624666,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326114720434,0,true,206034512704,206034512768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872908535118,0,false,-253756954752,-253756954688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326370914907,0,true,206246908800,206246908864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872652340645,0,false,-254079703552,-254079703488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052704359114,0,false,-47832794688,-47832794624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052810019258,0,false,-47722442048,-47722441984⟩
    { al := (844479/4096000), au := (52833/256000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨226688105447,226916007150⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205964032320,205964032384⟩ : DyadicInterval 40),(⟨-253649890240,-253649890176⟩ : DyadicInterval 40),(⟨738622171279,738622190608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206199874112,206199874176⟩ : DyadicInterval 40),(⟨-254008217984,-254008217920⟩ : DyadicInterval 40),(⟨738562678451,738562697780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58476345,87809719⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58474752,58474816⟩ : DyadicInterval 40),(⟨-58477952,-58477888⟩ : DyadicInterval 40),(⟨762123382041,762123401371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87806208,87806272⟩ : DyadicInterval 40),(⟨-87813248,-87813184⟩ : DyadicInterval 40),(⟨762123380059,762123399388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226603092658,226859287131⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206034512704,206034512768⟩ : DyadicInterval 40),(⟨-253756954752,-253756954688⟩ : DyadicInterval 40),(⟨738604401460,738604420790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206246908800,206246908864⟩ : DyadicInterval 40),(⟨-254079703552,-254079703488⟩ : DyadicInterval 40),(⟨738550802872,738550822202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47832794688,-47722441984⟩ : DyadicInterval 40),(⟨785984604608,786039800224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206104996480,206293926656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254151171072,-253864041664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1268_ok : ecellOkT e1268 = true := by decide +kernel
theorem e1268_pos {a z : ℝ} (ha1 : ((844479/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((52833/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1268 e1268_ok ha1 ha2 hz1 hz2 hz

-- box ['210483/1024000', '842781/4096000', '1999/2000', '3999/4000']  interval_lower 317647051/549755813888
noncomputable def e1269 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028116,0,true,205538011328,205538011392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227436,0,false,-253003103104,-253003103040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929820,0,true,205727038848,205727038912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325732,0,false,-253290007744,-253290007680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325403025915,0,true,205444272320,205444272384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873620229637,0,false,-252860872832,-252860872768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325687371745,0,true,205680131136,205680131200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873335883807,0,false,-253218800000,-253218799936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540772237,0,true,29144064,29144128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482483315,0,false,-29144896,-29144832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569980471,0,true,58351104,58351168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453275081,0,false,-58354304,-58354240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624679,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627004,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325459521728,0,true,205491138432,205491138496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873563733824,0,false,-252931979008,-252931978944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325715659431,0,true,205703592448,205703592512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873307596121,0,false,-253254414208,-253254414144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052974362826,0,false,-47550821760,-47550821696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053079694278,0,false,-47440840576,-47440840512⟩
    { al := (210483/1024000), au := (842781/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨226004400340,226232302044⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205444272320,205444272384⟩ : DyadicInterval 40),(⟨-252860872832,-252860872768⟩ : DyadicInterval 40),(⟨738752968404,738752987734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205680131136,205680131200⟩ : DyadicInterval 40),(⟨-253218800000,-253218799936⟩ : DyadicInterval 40),(⟨738693668635,738693687965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29144461,58352695⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29144064,29144128⟩ : DyadicInterval 40),(⟨-29144896,-29144832⟩ : DyadicInterval 40),(⟨762123383195,762123402524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58351104,58351168⟩ : DyadicInterval 40),(⟨-58354304,-58354240⟩ : DyadicInterval 40),(⟨762123382055,762123401384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225947893952,226204031655⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205491138432,205491138496⟩ : DyadicInterval 40),(⟨-252931979008,-252931978944⟩ : DyadicInterval 40),(⟨738741192413,738741211742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205703592448,205703592512⟩ : DyadicInterval 40),(⟨-253254414208,-253254414144⟩ : DyadicInterval 40),(⟨738687765078,738687784408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47550821760,-47440840512⟩ : DyadicInterval 40),(⟨785843803872,785898813760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205538011328,205727038912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253290007744,-253003103040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1269_ok : ecellOkT e1269 = true := by decide +kernel
theorem e1269_pos {a z : ℝ} (ha1 : ((210483/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((842781/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1269 e1269_ok ha1 ha2 hz1 hz2 hz

-- box ['842781/4096000', '84363/409600', '1999/2000', '3999/4000']  interval_lower 640570369/1099511627776
noncomputable def e1270 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929819,0,true,205727038848,205727038912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325733,0,false,-253290007744,-253290007680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831522,0,true,205916033920,205916033984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424030,0,false,-253576987264,-253576987200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325630813667,0,true,205633221440,205633221504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873392441885,0,false,-253147596864,-253147596800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325915216472,0,true,205869087040,205869087104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873108039080,0,false,-253505689216,-253505689152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540803503,0,true,29175296,29175360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482452049,0,false,-29176128,-29176064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570043017,0,true,58413632,58413696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453212535,0,false,-58416832,-58416768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624672,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627002,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325687366450,0,true,205680126784,205680126848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873335889102,0,false,-253218793344,-253218793280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325943532648,0,true,205892567872,205892567936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873079722904,0,false,-253541348544,-253541348480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052880554262,0,false,-47648780608,-47648780544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052986003606,0,false,-47538666560,-47538666496⟩
    { al := (842781/4096000), au := (84363/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨226232302043,226460203746⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205633221440,205633221504⟩ : DyadicInterval 40),(⟨-253147596864,-253147596800⟩ : DyadicInterval 40),(⟨738705469829,738705489158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205869087040,205869087104⟩ : DyadicInterval 40),(⟨-253505689216,-253505689152⟩ : DyadicInterval 40),(⟨738646096637,738646115967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29175727,58415241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29175296,29175360⟩ : DyadicInterval 40),(⟨-29176128,-29176064⟩ : DyadicInterval 40),(⟨762123383193,762123402522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58413632,58413696⟩ : DyadicInterval 40),(⟨-58416832,-58416768⟩ : DyadicInterval 40),(⟨762123382048,762123401377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226175738674,226431904872⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205680126784,205680126848⟩ : DyadicInterval 40),(⟨-253218793344,-253218793280⟩ : DyadicInterval 40),(⟨738693669720,738693689050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205892567872,205892567936⟩ : DyadicInterval 40),(⟨-253541348544,-253541348480⟩ : DyadicInterval 40),(⟨738640181030,738640200360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47648780608,-47538666496⟩ : DyadicInterval 40),(⟨785892716864,785947793184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205727038848,205916033984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253576987264,-253290007680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1270_ok : ecellOkT e1270 = true := by decide +kernel
theorem e1270_pos {a z : ℝ} (ha1 : ((842781/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84363/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1270 e1270_ok ha1 ha2 hz1 hz2 hz

-- box ['210483/1024000', '842781/4096000', '3999/4000', '1']  interval_lower 19822661/34359738368
noncomputable def e1271 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028116,0,true,205538011328,205538011392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227436,0,false,-253003103104,-253003103040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929820,0,true,205727038848,205727038912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325732,0,false,-253290007744,-253290007680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325459527015,0,true,205491142848,205491142912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873563728537,0,false,-252931985664,-252931985600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540804485,0,true,29176320,29176384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482451067,0,false,-29177152,-29177088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627001,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1325487771954,0,true,205514572672,205514572736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨873535483598,0,false,-252967536768,-252967536704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743938359,0,true,205727045952,205727046016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨873279317193,0,false,-253290018496,-253290018432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052962726373,0,false,-47562972544,-47562972480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053068082799,0,false,-47452964096,-47452964032⟩
    { al := (210483/1024000), au := (842781/4096000), zl := (3999/4000), zu := 1,
      A := ⟨226004400340,226232302044⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205491142848,205491142912⟩ : DyadicInterval 40),(⟨-252931985664,-252931985600⟩ : DyadicInterval 40),(⟨738741191293,738741210623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29176709⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29176320,29176384⟩ : DyadicInterval 40),(⟨-29177152,-29177088⟩ : DyadicInterval 40),(⟨762123383193,762123402522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨225976144178,226232310583⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205514572672,205514572736⟩ : DyadicInterval 40),(⟨-252967536768,-252967536704⟩ : DyadicInterval 40),(⟨738735302802,738735322132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727045952,205727046016⟩ : DyadicInterval 40),(⟨-253290018496,-253290018432⟩ : DyadicInterval 40),(⟨738681862597,738681881927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47562972544,-47452964032⟩ : DyadicInterval 40),(⟨785849865632,785904889152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨205538011328,205727038912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253290007744,-253003103040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1271_ok : ecellOkT e1271 = true := by decide +kernel
theorem e1271_pos {a z : ℝ} (ha1 : ((210483/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((842781/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1271 e1271_ok ha1 ha2 hz1 hz2 hz

-- box ['842781/4096000', '84363/409600', '3999/4000', '1']  interval_lower 39974857/68719476736
noncomputable def e1272 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325743929819,0,true,205727038848,205727038912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873279325733,0,false,-253290007744,-253290007680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831522,0,true,205916033920,205916033984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424030,0,false,-253576987264,-253576987200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325687371743,0,true,205680131136,205680131200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873335883809,0,false,-253218800000,-253218799936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540835759,0,true,29207552,29207616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482419793,0,false,-29208384,-29208320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627000,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1325715645159,0,true,205703580608,205703580672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨873307610393,0,false,-253254396224,-253254396160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971840065,0,true,205916040960,205916041024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨873051415487,0,false,-253576998016,-253576997952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052868894352,0,false,-47660956992,-47660956928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052974368699,0,false,-47550815616,-47550815552⟩
    { al := (842781/4096000), au := (84363/409600), zl := (3999/4000), zu := 1,
      A := ⟨226232302043,226460203746⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205727038848,205727038912⟩ : DyadicInterval 40),(⟨-253290007744,-253290007680⟩ : DyadicInterval 40),(⟨738681864393,738681883722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205680131136,205680131200⟩ : DyadicInterval 40),(⟨-253218800000,-253218799936⟩ : DyadicInterval 40),(⟨738693668636,738693687965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29207983⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29207552,29207616⟩ : DyadicInterval 40),(⟨-29208384,-29208320⟩ : DyadicInterval 40),(⟨762123383192,762123402521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨226204017383,226460212289⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205703580608,205703580672⟩ : DyadicInterval 40),(⟨-253254396224,-253254396160⟩ : DyadicInterval 40),(⟨738687768053,738687787382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916040960,205916041024⟩ : DyadicInterval 40),(⟨-253576998016,-253576997952⟩ : DyadicInterval 40),(⟨738634266486,738634285816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47660956992,-47550815552⟩ : DyadicInterval 40),(⟨785898791392,785953881376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨205727038848,205916033984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253576987264,-253290007680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1272_ok : ecellOkT e1272 = true := by decide +kernel
theorem e1272_pos {a z : ℝ} (ha1 : ((842781/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84363/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1272 e1272_ok ha1 ha2 hz1 hz2 hz

-- box ['84363/409600', '844479/4096000', '1999/2000', '3999/4000']  interval_lower 161466707/274877906944
noncomputable def e1273 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831521,0,true,205916033920,205916033984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424031,0,false,-253576987264,-253576987200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733224,0,true,206104996480,206104996544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522328,0,false,-253864041728,-253864041664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325858601419,0,true,205822138112,205822138176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873164654133,0,false,-253434395712,-253434395648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326143061198,0,true,206058010432,206058010496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872880194354,0,false,-253792653248,-253792653184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540834776,0,true,29206592,29206656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482420776,0,false,-29207424,-29207360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570105575,0,true,58476224,58476288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453149977,0,false,-58479360,-58479296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624665,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627001,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325915211175,0,true,205869082624,205869082688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873108044377,0,false,-253505682496,-253505682432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326171405861,0,true,206081510848,206081510912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872851849691,0,false,-253828357824,-253828357760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052786651246,0,false,-47746846912,-47746846848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052892218503,0,false,-47636599872,-47636599808⟩
    { al := (84363/409600), au := (844479/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨226460203745,226688105448⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205822138112,205822138176⟩ : DyadicInterval 40),(⟨-253434395712,-253434395648⟩ : DyadicInterval 40),(⟨738657921978,738657941308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206058010432,206058010496⟩ : DyadicInterval 40),(⟨-253792653248,-253792653184⟩ : DyadicInterval 40),(⟨738598475338,738598494667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29207000,58477799⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29206592,29206656⟩ : DyadicInterval 40),(⟨-29207424,-29207360⟩ : DyadicInterval 40),(⟨762123383192,762123402521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58476224,58476288⟩ : DyadicInterval 40),(⟨-58479360,-58479296⟩ : DyadicInterval 40),(⟨762123382009,762123401338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226403583399,226659778085⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205869082624,205869082688⟩ : DyadicInterval 40),(⟨-253505682496,-253505682432⟩ : DyadicInterval 40),(⟨738646097738,738646117068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206081510848,206081510912⟩ : DyadicInterval 40),(⟨-253828357824,-253828357760⟩ : DyadicInterval 40),(⟨738592547667,738592566996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47746846912,-47636599808⟩ : DyadicInterval 40),(⟨785941683520,785996826336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205916033920,206104996544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253864041728,-253576987200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1273_ok : ecellOkT e1273 = true := by decide +kernel
theorem e1273_pos {a z : ℝ} (ha1 : ((84363/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((844479/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1273 e1273_ok ha1 ha2 hz1 hz2 hz

-- box ['844479/4096000', '52833/256000', '1999/2000', '3999/4000']  interval_lower 651183867/1099511627776
noncomputable def e1274 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733223,0,true,206104996480,206104996544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522329,0,false,-253864041728,-253864041664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634926,0,true,206293926592,206293926656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620626,0,false,-254151171072,-254151171008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326086389170,0,true,206011022336,206011022400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872936866382,0,false,-253721269440,-253721269376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326370905925,0,true,206246901376,206246901440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872652349627,0,false,-254079692224,-254079692160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540866054,0,true,29237888,29237952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482389498,0,false,-29238720,-29238656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570168144,0,true,58538752,58538816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453087408,0,false,-58541952,-58541888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624659,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626999,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326143055892,0,true,206058006016,206058006080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872880199660,0,false,-253792646592,-253792646528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326399279081,0,true,206270421376,206270421440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872623976471,0,false,-254115441984,-254115441920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052692653774,0,false,-47845020544,-47845020480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052798338974,0,false,-47734640512,-47734640448⟩
    { al := (844479/4096000), au := (52833/256000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨226688105447,226916007150⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206011022336,206011022400⟩ : DyadicInterval 40),(⟨-253721269440,-253721269376⟩ : DyadicInterval 40),(⟨738610324866,738610344195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206246901376,206246901440⟩ : DyadicInterval 40),(⟨-254079692224,-254079692160⟩ : DyadicInterval 40),(⟨738550804735,738550824064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29238278,58540368⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29237888,29237952⟩ : DyadicInterval 40),(⟨-29238720,-29238656⟩ : DyadicInterval 40),(⟨762123383190,762123402519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58538752,58538816⟩ : DyadicInterval 40),(⟨-58541952,-58541888⟩ : DyadicInterval 40),(⟨762123382035,762123401364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226631428116,226887651305⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206058006016,206058006080⟩ : DyadicInterval 40),(⟨-253792646592,-253792646528⟩ : DyadicInterval 40),(⟨738598476468,738598495798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206270421376,206270421440⟩ : DyadicInterval 40),(⟨-254115441984,-254115441920⟩ : DyadicInterval 40),(⟨738544864947,738544884276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47845020544,-47734640448⟩ : DyadicInterval 40),(⟨785990703840,786045913152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206104996480,206293926656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254151171072,-253864041664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1274_ok : ecellOkT e1274 = true := by decide +kernel
theorem e1274_pos {a z : ℝ} (ha1 : ((844479/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((52833/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1274 e1274_ok ha1 ha2 hz1 hz2 hz

-- box ['84363/409600', '844479/4096000', '3999/4000', '1']  interval_lower 322445271/549755813888
noncomputable def e1275 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325971831521,0,true,205916033920,205916033984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873051424031,0,false,-253576987264,-253576987200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733224,0,true,206104996480,206104996544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522328,0,false,-253864041728,-253864041664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325915216470,0,true,205869087040,205869087104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873108039082,0,false,-253505689216,-253505689152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540867039,0,true,29238848,29238912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482388513,0,false,-29239680,-29239616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626998,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1325943518371,0,true,205892556032,205892556096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨873079737181,0,false,-253541330560,-253541330496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199741764,0,true,206105003520,206105003584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨872823513788,0,false,-253864052480,-253864052416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052774967857,0,false,-47759048896,-47759048832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052880560143,0,false,-47648774464,-47648774400⟩
    { al := (84363/409600), au := (844479/4096000), zl := (3999/4000), zu := 1,
      A := ⟨226460203745,226688105448⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205916033920,205916033984⟩ : DyadicInterval 40),(⟨-253576987264,-253576987200⟩ : DyadicInterval 40),(⟨738634268248,738634287578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205869087040,205869087104⟩ : DyadicInterval 40),(⟨-253505689216,-253505689152⟩ : DyadicInterval 40),(⟨738646096638,738646115968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29239263⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29238848,29238912⟩ : DyadicInterval 40),(⟨-29239680,-29239616⟩ : DyadicInterval 40),(⟨762123383190,762123402519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨226431890595,226688113988⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205892556032,205892556096⟩ : DyadicInterval 40),(⟨-253541330560,-253541330496⟩ : DyadicInterval 40),(⟨738640184012,738640203342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206105003520,206105003584⟩ : DyadicInterval 40),(⟨-253864052480,-253864052416⟩ : DyadicInterval 40),(⟨738586621034,738586640364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47759048896,-47648774400⟩ : DyadicInterval 40),(⟨785947770816,786002927328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨205916033920,206104996544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253864041728,-253576987200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1275_ok : ecellOkT e1275 = true := by decide +kernel
theorem e1275_pos {a z : ℝ} (ha1 : ((84363/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((844479/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1275 e1275_ok ha1 ha2 hz1 hz2 hz

-- box ['844479/4096000', '52833/256000', '3999/4000', '1']  interval_lower 325102001/549755813888
noncomputable def e1276 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326199733223,0,true,206104996480,206104996544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872823522329,0,false,-253864041728,-253864041664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634926,0,true,206293926592,206293926656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620626,0,false,-254151171072,-254151171008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326143061196,0,true,206058010432,206058010496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872880194356,0,false,-253792653248,-253792653184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540898324,0,true,29270144,29270208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482357228,0,false,-29270976,-29270912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626996,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1326171391579,0,true,206081499008,206081499072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨872851863973,0,false,-253828339776,-253828339712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427643475,0,true,206293933632,206293933696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨872595612077,0,false,-254151181888,-254151181824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052680946881,0,false,-47857248192,-47857248128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052786657136,0,false,-47746840768,-47746840704⟩
    { al := (844479/4096000), au := (52833/256000), zl := (3999/4000), zu := 1,
      A := ⟨226688105447,226916007150⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206104996480,206104996544⟩ : DyadicInterval 40),(⟨-253864041728,-253864041664⟩ : DyadicInterval 40),(⟨738586622799,738586642129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206058010432,206058010496⟩ : DyadicInterval 40),(⟨-253792653248,-253792653184⟩ : DyadicInterval 40),(⟨738598475338,738598494668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29270548⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29270144,29270208⟩ : DyadicInterval 40),(⟨-29270976,-29270912⟩ : DyadicInterval 40),(⟨762123383188,762123402517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨226659763803,226916015699⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206081499008,206081499072⟩ : DyadicInterval 40),(⟨-253828339776,-253828339712⟩ : DyadicInterval 40),(⟨738592550630,738592569960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293933632,206293933696⟩ : DyadicInterval 40),(⟨-254151181888,-254151181824⟩ : DyadicInterval 40),(⟨738538926224,738538945554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47857248192,-47746840704⟩ : DyadicInterval 40),(⟨785996803968,786052026976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨206104996480,206293926656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254151171072,-253864041664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1276_ok : ecellOkT e1276 = true := by decide +kernel
theorem e1276_pos {a z : ℝ} (ha1 : ((844479/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((52833/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1276 e1276_ok ha1 ha2 hz1 hz2 hz

-- box ['52833/256000', '846177/4096000', '999/1000', '3997/4000']  interval_lower 164621491/274877906944
noncomputable def e1277 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634925,0,true,206293926592,206293926656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620627,0,false,-254151171072,-254151171008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536628,0,true,206482824192,206482824256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718924,0,false,-254438375488,-254438375424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326200718917,0,true,206105813696,206105813760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872822536635,0,false,-253865283392,-253865283328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326485178697,0,true,206341625088,206341625152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872538076855,0,false,-254223681344,-254223681280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599435566,0,true,87804224,87804288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423819986,0,false,-87811328,-87811264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628831531,0,true,117197504,117197568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394424021,0,false,-117210048,-117209984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615282,0,false,-12544,-12480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620764,0,false,-7040,-6976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326314172948,0,true,206199870848,206199870912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872709082604,0,false,-254008212928,-254008212864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326570367198,0,true,206412234816,206412234880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872452888354,0,false,-254331035200,-254331035136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052622018020,0,false,-47918800320,-47918800256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052727771020,0,false,-47808342080,-47808342016⟩
    { al := (52833/256000), au := (846177/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨226916007149,227143908852⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206105813696,206105813760⟩ : DyadicInterval 40),(⟨-253865283392,-253865283328⟩ : DyadicInterval 40),(⟨738586416604,738586435933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206341625088,206341625152⟩ : DyadicInterval 40),(⟨-254223681344,-254223681280⟩ : DyadicInterval 40),(⟨738526877564,738526896893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87807790,117203755⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87804224,87804288⟩ : DyadicInterval 40),(⟨-87811328,-87811264⟩ : DyadicInterval 40),(⟨762123380091,762123399420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117197504,117197568⟩ : DyadicInterval 40),(⟨-117210048,-117209984⟩ : DyadicInterval 40),(⟨762123377330,762123396659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12544,-6976⟩ : DyadicInterval 40),(⟨762123387104,762123409152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226802545172,227058739422⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206199870848,206199870912⟩ : DyadicInterval 40),(⟨-254008212928,-254008212864⟩ : DyadicInterval 40),(⟨738562679245,738562698574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206412234816,206412234880⟩ : DyadicInterval 40),(⟨-254331035200,-254331035136⟩ : DyadicInterval 40),(⟨738509032159,738509051489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47918800320,-47808342016⟩ : DyadicInterval 40),(⟨786027554624,786082803040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206293926592,206482824256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254438375488,-254151171008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1277_ok : ecellOkT e1277 = true := by decide +kernel
theorem e1277_pos {a z : ℝ} (ha1 : ((52833/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((846177/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1277 e1277_ok ha1 ha2 hz1 hz2 hz

-- box ['846177/4096000', '423513/2048000', '999/1000', '3997/4000']  interval_lower 663851233/1099511627776
noncomputable def e1278 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536627,0,true,206482824192,206482824256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718925,0,false,-254438375488,-254438375424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438330,0,true,206671689408,206671689472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817222,0,false,-254725654912,-254725654848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326428392718,0,true,206294554688,206294554752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872594862834,0,false,-254152125952,-254152125888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326712909473,0,true,206530372928,206530372992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872310346079,0,false,-254510689280,-254510689216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599529432,0,true,87898112,87898176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423726120,0,false,-87905216,-87905152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628956713,0,true,117322624,117322688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394298839,0,false,-117335232,-117335168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615255,0,false,-12544,-12480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620749,0,false,-7040,-6976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326541960691,0,true,206388690176,206388690240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872481294861,0,false,-254295236416,-254295236352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326798183445,0,true,206601041344,206601041408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872225072107,0,false,-254618178880,-254618178816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052527878734,0,false,-48017137536,-48017137472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052633749670,0,false,-47906546176,-47906546112⟩
    { al := (846177/4096000), au := (423513/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨227143908851,227371810554⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206294554688,206294554752⟩ : DyadicInterval 40),(⟨-254152125952,-254152125888⟩ : DyadicInterval 40),(⟨738538769343,738538788673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206530372928,206530372992⟩ : DyadicInterval 40),(⟨-254510689280,-254510689216⟩ : DyadicInterval 40),(⟨738479156787,738479176116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87901656,117328937⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87898112,87898176⟩ : DyadicInterval 40),(⟨-87905216,-87905152⟩ : DyadicInterval 40),(⟨762123380076,762123399405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117322624,117322688⟩ : DyadicInterval 40),(⟨-117335232,-117335168⟩ : DyadicInterval 40),(⟨762123377335,762123396665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12544,-6976⟩ : DyadicInterval 40),(⟨762123387104,762123409152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227030332915,227286555669⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206388690176,206388690240⟩ : DyadicInterval 40),(⟨-254295236416,-254295236352⟩ : DyadicInterval 40),(⟨738514983570,738515002899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206601041344,206601041408⟩ : DyadicInterval 40),(⟨-254618178880,-254618178816⟩ : DyadicInterval 40),(⟨738461275027,738461294357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48017137536,-47906546112⟩ : DyadicInterval 40),(⟨786076656672,786131971648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206482824192,206671689472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254725654912,-254438375424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1278_ok : ecellOkT e1278 = true := by decide +kernel
theorem e1278_pos {a z : ℝ} (ha1 : ((846177/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((423513/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1278 e1278_ok ha1 ha2 hz1 hz2 hz

-- box ['52833/256000', '846177/4096000', '3997/4000', '1999/2000']  interval_lower 82188023/137438953472
noncomputable def e1279 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634925,0,true,206293926592,206293926656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620627,0,false,-254151171072,-254151171008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536628,0,true,206482824192,206482824256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718924,0,false,-254438375488,-254438375424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326257447919,0,true,206152844928,206152844992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872765807633,0,false,-253936748352,-253936748288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326541964674,0,true,206388693504,206388693568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872481290878,0,false,-254295241408,-254295241344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570166687,0,true,58537344,58537408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453088865,0,false,-58540480,-58540416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599531365,0,true,87900032,87900096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423724187,0,false,-87907136,-87907072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620748,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624660,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326342536676,0,true,206223384064,206223384128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872680718876,0,false,-254043948544,-254043948480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326598759636,0,true,206435767296,206435767360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872424495916,0,false,-254366817472,-254366817408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052610290715,0,false,-47931050112,-47931050048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052716068791,0,false,-47820564416,-47820564352⟩
    { al := (52833/256000), au := (846177/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨226916007149,227143908852⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206152844928,206152844992⟩ : DyadicInterval 40),(⟨-253936748352,-253936748288⟩ : DyadicInterval 40),(⟨738574549040,738574568369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206388693504,206388693568⟩ : DyadicInterval 40),(⟨-254295241408,-254295241344⟩ : DyadicInterval 40),(⟨738514982708,738515002038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58538911,87903589⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58537344,58537408⟩ : DyadicInterval 40),(⟨-58540480,-58540416⟩ : DyadicInterval 40),(⟨762123382003,762123401332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87900032,87900096⟩ : DyadicInterval 40),(⟨-87907136,-87907072⟩ : DyadicInterval 40),(⟨762123380076,762123399405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226830908900,227087131860⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206223384064,206223384128⟩ : DyadicInterval 40),(⟨-254043948544,-254043948480⟩ : DyadicInterval 40),(⟨738556742967,738556762296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206435767296,206435767360⟩ : DyadicInterval 40),(⟨-254366817472,-254366817408⟩ : DyadicInterval 40),(⟨738503082949,738503102278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47931050112,-47820564352⟩ : DyadicInterval 40),(⟨786033665792,786088927936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206293926592,206482824256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254438375488,-254151171008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1279_ok : ecellOkT e1279 = true := by decide +kernel
theorem e1279_pos {a z : ℝ} (ha1 : ((52833/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((846177/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1279 e1279_ok ha1 ha2 hz1 hz2 hz

-- box ['846177/4096000', '423513/2048000', '3997/4000', '1999/2000']  interval_lower 331432829/549755813888
noncomputable def e1280 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536627,0,true,206482824192,206482824256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718925,0,false,-254438375488,-254438375424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438330,0,true,206671689408,206671689472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817222,0,false,-254725654912,-254725654848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326485178695,0,true,206341625088,206341625152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872538076857,0,false,-254223681344,-254223681280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326769752425,0,true,206577480448,206577480512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872253503127,0,false,-254582339840,-254582339776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570229267,0,true,58599872,58599936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453026285,0,false,-58603072,-58603008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599625253,0,true,87993920,87993984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423630299,0,false,-88001024,-88000960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620733,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624653,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326570352906,0,true,206412222976,206412223040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872452902646,0,false,-254331017216,-254331017152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326826604367,0,true,206624593344,206624593408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872196651185,0,false,-254654006400,-254654006336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052516127885,0,false,-48029412992,-48029412928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052622023924,0,false,-47918794176,-47918794112⟩
    { al := (846177/4096000), au := (423513/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨227143908851,227371810554⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206341625088,206341625152⟩ : DyadicInterval 40),(⟨-254223681344,-254223681280⟩ : DyadicInterval 40),(⟨738526877564,738526896894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206577480448,206577480512⟩ : DyadicInterval 40),(⟨-254582339840,-254582339776⟩ : DyadicInterval 40),(⟨738467237715,738467257044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58601491,87997477⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58599872,58599936⟩ : DyadicInterval 40),(⟨-58603072,-58603008⟩ : DyadicInterval 40),(⟨762123382028,762123401357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87993920,87993984⟩ : DyadicInterval 40),(⟨-88001024,-88000960⟩ : DyadicInterval 40),(⟨762123380060,762123399390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227058725130,227314976591⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206412222976,206412223040⟩ : DyadicInterval 40),(⟨-254331017216,-254331017152⟩ : DyadicInterval 40),(⟨738509035161,738509054491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206624593344,206624593408⟩ : DyadicInterval 40),(⟨-254654006400,-254654006336⟩ : DyadicInterval 40),(⟨738455313720,738455333050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48029412992,-47918794112⟩ : DyadicInterval 40),(⟨786082780672,786138109376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206482824192,206671689472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254725654912,-254438375424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1280_ok : ecellOkT e1280 = true := by decide +kernel
theorem e1280_pos {a z : ℝ} (ha1 : ((846177/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((423513/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1280 e1280_ok ha1 ha2 hz1 hz2 hz

-- box ['423513/2048000', '6783/32768', '999/1000', '3997/4000']  interval_lower 669237463/1099511627776
noncomputable def e1281 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438329,0,true,206671689408,206671689472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817223,0,false,-254725654912,-254725654848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326656066518,0,true,206483263360,206483263424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872367189034,0,false,-254439043392,-254439043328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326940640248,0,true,206719088320,206719088384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872082615304,0,false,-254797772096,-254797772032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599623316,0,true,87992000,87992064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423632236,0,false,-87999104,-87999040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629081919,0,true,117447808,117447872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394173633,0,false,-117460480,-117460416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615229,0,false,-12608,-12544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620734,0,false,-7104,-7040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326769748446,0,true,206577477120,206577477184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872253507106,0,false,-254582334784,-254582334720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327025999687,0,true,206789815424,206789815488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871997255865,0,false,-254905397568,-254905397504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052433645044,0,false,-48115582080,-48115582016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052539633933,0,false,-48004857664,-48004857600⟩
    { al := (423513/2048000), au := (6783/32768), zl := (999/1000), zu := (3997/4000),
      A := ⟨227371810553,227599712256⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206483263360,206483263424⟩ : DyadicInterval 40),(⟨-254439043392,-254439043328⟩ : DyadicInterval 40),(⟨738491072808,738491092137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206719088320,206719088384⟩ : DyadicInterval 40),(⟨-254797772096,-254797772032⟩ : DyadicInterval 40),(⟨738431386746,738431406076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87995540,117454143⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87992000,87992064⟩ : DyadicInterval 40),(⟨-87999104,-87999040⟩ : DyadicInterval 40),(⟨762123380061,762123399390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117447808,117447872⟩ : DyadicInterval 40),(⟨-117460480,-117460416⟩ : DyadicInterval 40),(⟨762123377340,762123396670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12608,-7040⟩ : DyadicInterval 40),(⟨762123387136,762123409184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227258120670,227514371911⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206577477120,206577477184⟩ : DyadicInterval 40),(⟨-254582334784,-254582334720⟩ : DyadicInterval 40),(⟨738467238552,738467257881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206789815424,206789815488⟩ : DyadicInterval 40),(⟨-254905397568,-254905397504⟩ : DyadicInterval 40),(⟨738413468605,738413487935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48115582080,-48004857600⟩ : DyadicInterval 40),(⟨786125812416,786181193920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206671689408,206860522240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255013009472,-254725654848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1281_ok : ecellOkT e1281 = true := by decide +kernel
theorem e1281_pos {a z : ℝ} (ha1 : ((423513/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6783/32768 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1281 e1281_ok ha1 ha2 hz1 hz2 hz

-- box ['6783/32768', '212181/1024000', '999/1000', '3997/4000']  interval_lower 674643963/1099511627776
noncomputable def e1282 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241735,0,true,207049322496,207049322560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013817,0,false,-255300439104,-255300439040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883740319,0,true,206671939648,206671939712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872139515233,0,false,-254726035648,-254726035584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327168371025,0,true,206907771328,206907771392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871854884527,0,false,-255084929920,-255084929856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599717219,0,true,88085888,88085952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423538333,0,false,-88092992,-88092928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629207149,0,true,117573056,117573120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099394048403,0,false,-117585664,-117585600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615202,0,false,-12608,-12544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620719,0,false,-7104,-7040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326997536201,0,true,206766231616,206766231680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872025719351,0,false,-254869508160,-254869508096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327253815928,0,true,206978557056,206978557120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871769439624,0,false,-255192691264,-255192691200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052339316948,0,false,-48214134144,-48214134080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052445423814,0,false,-48103276544,-48103276480⟩
    { al := (6783/32768), au := (212181/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨227599712256,227827613959⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671939648,206671939712⟩ : DyadicInterval 40),(⟨-254726035648,-254726035584⟩ : DyadicInterval 40),(⟨738443326999,738443346328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206907771328,206907771392⟩ : DyadicInterval 40),(⟨-255084929920,-255084929856⟩ : DyadicInterval 40),(⟨738383567443,738383586772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88089443,117579373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88085888,88085952⟩ : DyadicInterval 40),(⟨-88092992,-88092928⟩ : DyadicInterval 40),(⟨762123380046,762123399375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117573056,117573120⟩ : DyadicInterval 40),(⟨-117585664,-117585600⟩ : DyadicInterval 40),(⟨762123377281,762123396611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12608,-7040⟩ : DyadicInterval 40),(⟨762123387136,762123409184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227485908425,227742188152⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206766231616,206766231680⟩ : DyadicInterval 40),(⟨-254869508160,-254869508096⟩ : DyadicInterval 40),(⟨738419444269,738419463598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206978557056,206978557120⟩ : DyadicInterval 40),(⟨-255192691264,-255192691200⟩ : DyadicInterval 40),(⟨738365612879,738365632209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48214134144,-48103276480⟩ : DyadicInterval 40),(⟨786175021856,786230469952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206860522176,207049322560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255300439104,-255013009408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1282_ok : ecellOkT e1282 = true := by decide +kernel
theorem e1282_pos {a z : ℝ} (ha1 : ((6783/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((212181/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1282 e1282_ok ha1 ha2 hz1 hz2 hz

-- box ['423513/2048000', '6783/32768', '3997/4000', '1999/2000']  interval_lower 668248323/1099511627776
noncomputable def e1283 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438329,0,true,206671689408,206671689472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817223,0,false,-254725654912,-254725654848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326712909471,0,true,206530372928,206530372992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872310346081,0,false,-254510689280,-254510689216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326997540177,0,true,206766234944,206766235008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872025715375,0,false,-254869513216,-254869513152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570291857,0,true,58662464,58662528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452963695,0,false,-58665664,-58665600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599719160,0,true,88087808,88087872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423536392,0,false,-88094976,-88094912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620718,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624646,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326798169149,0,true,206601029504,206601029568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872225086403,0,false,-254618160832,-254618160768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327054449093,0,true,206813387008,206813387072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871968806459,0,false,-254941270336,-254941270272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052421870628,0,false,-48127883264,-48127883200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052527884645,0,false,-48017131328,-48017131264⟩
    { al := (423513/2048000), au := (6783/32768), zl := (3997/4000), zu := (1999/2000),
      A := ⟨227371810553,227599712256⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206530372928,206530372992⟩ : DyadicInterval 40),(⟨-254510689280,-254510689216⟩ : DyadicInterval 40),(⟨738479156787,738479176116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206766234944,206766235008⟩ : DyadicInterval 40),(⟨-254869513216,-254869513152⟩ : DyadicInterval 40),(⟨738419443431,738419462760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58664081,88091384⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58662464,58662528⟩ : DyadicInterval 40),(⟨-58665664,-58665600⟩ : DyadicInterval 40),(⟨762123382021,762123401351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88087808,88087872⟩ : DyadicInterval 40),(⟨-88094976,-88094912⟩ : DyadicInterval 40),(⟨762123380077,762123399407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227286541373,227542821317⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206601029504,206601029568⟩ : DyadicInterval 40),(⟨-254618160832,-254618160768⟩ : DyadicInterval 40),(⟨738461278011,738461297340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206813387008,206813387072⟩ : DyadicInterval 40),(⟨-254941270336,-254941270272⟩ : DyadicInterval 40),(⟨738407495137,738407514467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48127883264,-48017131264⟩ : DyadicInterval 40),(⟨786131949248,786187344512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206671689408,206860522240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255013009472,-254725654848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1283_ok : ecellOkT e1283 = true := by decide +kernel
theorem e1283_pos {a z : ℝ} (ha1 : ((423513/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6783/32768 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1283 e1283_ok ha1 ha2 hz1 hz2 hz

-- box ['6783/32768', '212181/1024000', '3997/4000', '1999/2000']  interval_lower 336825561/549755813888
noncomputable def e1284 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241735,0,true,207049322496,207049322560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013817,0,false,-255300439104,-255300439040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326940640247,0,true,206719088320,206719088384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872082615305,0,false,-254797772096,-254797772032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327225327929,0,true,206954957056,206954957120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871797927623,0,false,-255156761600,-255156761536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570354459,0,true,58725056,58725120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452901093,0,false,-58728256,-58728192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599813085,0,true,88181760,88181824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423442467,0,false,-88188864,-88188800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620703,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624640,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327025985386,0,true,206789803584,206789803648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871997270166,0,false,-254905379520,-254905379456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327282293822,0,true,207002148224,207002148288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871740961730,0,false,-255228609344,-255228609280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052327518940,0,false,-48226461120,-48226461056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052433650963,0,false,-48115575936,-48115575872⟩
    { al := (6783/32768), au := (212181/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨227599712256,227827613959⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206719088320,206719088384⟩ : DyadicInterval 40),(⟨-254797772096,-254797772032⟩ : DyadicInterval 40),(⟨738431386747,738431406076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206954957056,206954957120⟩ : DyadicInterval 40),(⟨-255156761600,-255156761536⟩ : DyadicInterval 40),(⟨738371599830,738371619160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58726683,88185309⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58725056,58725120⟩ : DyadicInterval 40),(⟨-58728256,-58728192⟩ : DyadicInterval 40),(⟨762123382015,762123401344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88181760,88181824⟩ : DyadicInterval 40),(⟨-88188864,-88188800⟩ : DyadicInterval 40),(⟨762123380030,762123399360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227514357610,227770666046⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206789803584,206789803648⟩ : DyadicInterval 40),(⟨-254905379520,-254905379456⟩ : DyadicInterval 40),(⟨738413471596,738413490926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207002148224,207002148288⟩ : DyadicInterval 40),(⟨-255228609344,-255228609280⟩ : DyadicInterval 40),(⟨738359627248,738359646577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48226461120,-48115575872⟩ : DyadicInterval 40),(⟨786181171552,786236633440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206860522176,207049322560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255300439104,-255013009408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1284_ok : ecellOkT e1284 = true := by decide +kernel
theorem e1284_pos {a z : ℝ} (ha1 : ((6783/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((212181/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1284 e1284_ok ha1 ha2 hz1 hz2 hz

-- box ['52833/256000', '846177/4096000', '1999/2000', '3999/4000']  interval_lower 656521587/1099511627776
noncomputable def e1285 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634925,0,true,206293926592,206293926656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620627,0,false,-254151171072,-254151171008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536628,0,true,206482824192,206482824256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718924,0,false,-254438375488,-254438375424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326314176921,0,true,206199874112,206199874176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872709078631,0,false,-254008217984,-254008217920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326598750651,0,true,206435759872,206435759936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872424504901,0,false,-254366806144,-254366806080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540897338,0,true,29269120,29269184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482358214,0,false,-29269952,-29269888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570230727,0,true,58601344,58601408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453024825,0,false,-58604544,-58604480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624652,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626997,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326370900620,0,true,206246896960,206246897024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872652354932,0,false,-254079685504,-254079685440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326627152292,0,true,206459299456,206459299520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872396103260,0,false,-254402601152,-254402601088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052598561853,0,false,-47943301632,-47943301568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052704365011,0,false,-47832788544,-47832788480⟩
    { al := (52833/256000), au := (846177/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨226916007149,227143908852⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206199874112,206199874176⟩ : DyadicInterval 40),(⟨-254008217984,-254008217920⟩ : DyadicInterval 40),(⟨738562678451,738562697781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206435759872,206435759936⟩ : DyadicInterval 40),(⟨-254366806144,-254366806080⟩ : DyadicInterval 40),(⟨738503084816,738503104145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29269562,58602951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29269120,29269184⟩ : DyadicInterval 40),(⟨-29269952,-29269888⟩ : DyadicInterval 40),(⟨762123383188,762123402517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58601344,58601408⟩ : DyadicInterval 40),(⟨-58604544,-58604480⟩ : DyadicInterval 40),(⟨762123382028,762123401357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨226859272844,227115524516⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206246896960,206246897024⟩ : DyadicInterval 40),(⟨-254079685504,-254079685440⟩ : DyadicInterval 40),(⟨738550805842,738550825172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206459299456,206459299520⟩ : DyadicInterval 40),(⟨-254402601152,-254402601088⟩ : DyadicInterval 40),(⟨738497132912,738497152242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47943301632,-47832788480⟩ : DyadicInterval 40),(⟨786039777856,786095053696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206293926592,206482824256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254438375488,-254151171008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1285_ok : ecellOkT e1285 = true := by decide +kernel
theorem e1285_pos {a z : ℝ} (ha1 : ((52833/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((846177/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1285 e1285_ok ha1 ha2 hz1 hz2 hz

-- box ['846177/4096000', '423513/2048000', '1999/2000', '3999/4000']  interval_lower 661879581/1099511627776
noncomputable def e1286 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536627,0,true,206482824192,206482824256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718925,0,false,-254438375488,-254438375424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438330,0,true,206671689408,206671689472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817222,0,false,-254725654912,-254725654848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326541964672,0,true,206388693504,206388693568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872481290880,0,false,-254295241408,-254295241344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1326826595378,0,true,206624585920,206624585984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨872196660174,0,false,-254653995072,-254653995008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540928629,0,true,29300416,29300480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482326923,0,false,-29301248,-29301184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570293320,0,true,58663936,58664000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452962232,0,false,-58667136,-58667072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624645,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626996,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326598745344,0,true,206435755456,206435755520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872424510208,0,false,-254366799424,-254366799360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1326855025508,0,true,206648145088,206648145152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨872168230044,0,false,-254689835328,-254689835264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052504375477,0,false,-48041690240,-48041690176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052610296619,0,false,-47931043968,-47931043904⟩
    { al := (846177/4096000), au := (423513/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨227143908851,227371810554⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206388693504,206388693568⟩ : DyadicInterval 40),(⟨-254295241408,-254295241344⟩ : DyadicInterval 40),(⟨738514982709,738515002038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206624585920,206624585984⟩ : DyadicInterval 40),(⟨-254653995072,-254653995008⟩ : DyadicInterval 40),(⟨738455315592,738455334922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29300853,58665544⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29300416,29300480⟩ : DyadicInterval 40),(⟨-29301248,-29301184⟩ : DyadicInterval 40),(⟨762123383187,762123402516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58663936,58664000⟩ : DyadicInterval 40),(⟨-58667136,-58667072⟩ : DyadicInterval 40),(⟨762123382021,762123401350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227087117568,227343397732⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206435755456,206435755520⟩ : DyadicInterval 40),(⟨-254366799424,-254366799360⟩ : DyadicInterval 40),(⟨738503085926,738503105255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206648145088,206648145152⟩ : DyadicInterval 40),(⟨-254689835328,-254689835264⟩ : DyadicInterval 40),(⟨738449351545,738449370875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48041690240,-47931043904⟩ : DyadicInterval 40),(⟨786088905568,786144248000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206482824192,206671689472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254725654912,-254438375424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1286_ok : ecellOkT e1286 = true := by decide +kernel
theorem e1286_pos {a z : ℝ} (ha1 : ((846177/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((423513/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1286 e1286_ok ha1 ha2 hz1 hz2 hz

-- box ['52833/256000', '846177/4096000', '3999/4000', '1']  interval_lower 655537831/1099511627776
noncomputable def e1287 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326427634925,0,true,206293926592,206293926656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872595620627,0,false,-254151171072,-254151171008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536628,0,true,206482824192,206482824256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718924,0,false,-254438375488,-254438375424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326370905923,0,true,206246901376,206246901440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872652349629,0,false,-254079692224,-254079692160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540929616,0,true,29301440,29301504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482325936,0,false,-29302272,-29302208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626995,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1326399264794,0,true,206270409536,206270409600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨872623990758,0,false,-254115424000,-254115423936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655545168,0,true,206482831296,206482831360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨872367710384,0,false,-254438386240,-254438386176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052586831434,0,false,-47955554944,-47955554880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052692659672,0,false,-47845014400,-47845014336⟩
    { al := (52833/256000), au := (846177/4096000), zl := (3999/4000), zu := 1,
      A := ⟨226916007149,227143908852⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206293926592,206293926656⟩ : DyadicInterval 40),(⟨-254151171072,-254151171008⟩ : DyadicInterval 40),(⟨738538927969,738538947299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206246901376,206246901440⟩ : DyadicInterval 40),(⟨-254079692224,-254079692160⟩ : DyadicInterval 40),(⟨738550804735,738550824065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29301840⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29301440,29301504⟩ : DyadicInterval 40),(⟨-29302272,-29302208⟩ : DyadicInterval 40),(⟨762123383187,762123402516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨226887637018,227143917392⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206270409536,206270409600⟩ : DyadicInterval 40),(⟨-254115424000,-254115423936⟩ : DyadicInterval 40),(⟨738544867944,738544887273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482831296,206482831360⟩ : DyadicInterval 40),(⟨-254438386240,-254438386176⟩ : DyadicInterval 40),(⟨738491182049,738491201379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47955554944,-47845014336⟩ : DyadicInterval 40),(⟨786045890784,786101180352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨206293926592,206482824256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254438375488,-254151171008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1287_ok : ecellOkT e1287 = true := by decide +kernel
theorem e1287_pos {a z : ℝ} (ha1 : ((52833/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((846177/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1287 e1287_ok ha1 ha2 hz1 hz2 hz

-- box ['846177/4096000', '423513/2048000', '3999/4000', '1']  interval_lower 660892211/1099511627776
noncomputable def e1288 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326655536627,0,true,206482824192,206482824256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872367718925,0,false,-254438375488,-254438375424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438330,0,true,206671689408,206671689472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817222,0,false,-254725654912,-254725654848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326598750649,0,true,206435759872,206435759936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872424504903,0,false,-254366806144,-254366806080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540960914,0,true,29332736,29332800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482294638,0,false,-29333568,-29333504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626993,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1326627137999,0,true,206459287616,206459287680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨872396117553,0,false,-254402583104,-254402583040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883446877,0,true,206671696448,206671696512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨872139808675,0,false,-254725665728,-254725665664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052492621505,0,false,-48053969216,-48053969152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052598567759,0,false,-47943295488,-47943295424⟩
    { al := (846177/4096000), au := (423513/2048000), zl := (3999/4000), zu := 1,
      A := ⟨227143908851,227371810554⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206482824192,206482824256⟩ : DyadicInterval 40),(⟨-254438375488,-254438375424⟩ : DyadicInterval 40),(⟨738491183860,738491203189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206435759872,206435759936⟩ : DyadicInterval 40),(⟨-254366806144,-254366806080⟩ : DyadicInterval 40),(⟨738503084816,738503104146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29333138⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29332736,29332800⟩ : DyadicInterval 40),(⟨-29333568,-29333504⟩ : DyadicInterval 40),(⟨762123383185,762123402514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨227115510223,227371819101⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206459287616,206459287680⟩ : DyadicInterval 40),(⟨-254402583104,-254402583040⟩ : DyadicInterval 40),(⟨738497135890,738497155220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671696448,206671696512⟩ : DyadicInterval 40),(⟨-254725665728,-254725665664⟩ : DyadicInterval 40),(⟨738443388603,738443407933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48053969216,-47943295424⟩ : DyadicInterval 40),(⟨786095031328,786150387488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨206482824192,206671689472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-254725654912,-254438375424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1288_ok : ecellOkT e1288 = true := by decide +kernel
theorem e1288_pos {a z : ℝ} (ha1 : ((846177/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((423513/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1288 e1288_ok ha1 ha2 hz1 hz2 hz

-- box ['423513/2048000', '6783/32768', '1999/2000', '3999/4000']  interval_lower 333628961/549755813888
noncomputable def e1289 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438329,0,true,206671689408,206671689472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817223,0,false,-254725654912,-254725654848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326769752423,0,true,206577480384,206577480448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872253503129,0,false,-254582339840,-254582339776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327054440105,0,true,206813379520,206813379584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871968815447,0,false,-254941259008,-254941258944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540959925,0,true,29331712,29331776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482295627,0,false,-29332544,-29332480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570355927,0,true,58726528,58726592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452899625,0,false,-58729728,-58729664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624639,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626994,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1326826590064,0,true,206624581504,206624581568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨872196665488,0,false,-254653988352,-254653988288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327082898719,0,true,206836958272,206836958336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871940356833,0,false,-254977144576,-254977144512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052410094649,0,false,-48140186240,-48140186176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052516133800,0,false,-48029406784,-48029406720⟩
    { al := (423513/2048000), au := (6783/32768), zl := (1999/2000), zu := (3999/4000),
      A := ⟨227371810553,227599712256⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206577480384,206577480448⟩ : DyadicInterval 40),(⟨-254582339840,-254582339776⟩ : DyadicInterval 40),(⟨738467237754,738467257083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206813379520,206813379584⟩ : DyadicInterval 40),(⟨-254941259008,-254941258944⟩ : DyadicInterval 40),(⟨738407497051,738407516381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29332149,58728151⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29331712,29331776⟩ : DyadicInterval 40),(⟨-29332544,-29332480⟩ : DyadicInterval 40),(⟨762123383185,762123402514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58726528,58726592⟩ : DyadicInterval 40),(⟨-58729728,-58729664⟩ : DyadicInterval 40),(⟨762123382015,762123401344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227314962288,227571270943⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206624581504,206624581568⟩ : DyadicInterval 40),(⟨-254653988352,-254653988288⟩ : DyadicInterval 40),(⟨738455316706,738455336036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206836958272,206836958336⟩ : DyadicInterval 40),(⟨-254977144576,-254977144512⟩ : DyadicInterval 40),(⟨738401520861,738401540191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48140186240,-48029406720⟩ : DyadicInterval 40),(⟨786138086976,786193496000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206671689408,206860522240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255013009472,-254725654848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1289_ok : ecellOkT e1289 = true := by decide +kernel
theorem e1289_pos {a z : ℝ} (ha1 : ((423513/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6783/32768 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1289 e1289_ok ha1 ha2 hz1 hz2 hz

-- box ['6783/32768', '212181/1024000', '1999/2000', '3999/4000']  interval_lower 672657259/1099511627776
noncomputable def e1290 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241735,0,true,207049322496,207049322560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013817,0,false,-255300439104,-255300439040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326997540175,0,true,206766234944,206766235008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872025715377,0,false,-254869513216,-254869513152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327282284832,0,true,207002140800,207002140864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871740970720,0,false,-255228598016,-255228597952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540991226,0,true,29363008,29363072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482264326,0,false,-29363904,-29363840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570418544,0,true,58789184,58789248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452837008,0,false,-58792384,-58792320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624632,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626992,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327054434790,0,true,206813375168,206813375232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871968820762,0,false,-254941252288,-254941252224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327310771940,0,true,207025739072,207025739136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871712483612,0,false,-255264528896,-255264528832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052315719364,0,false,-48238789824,-48238789760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052421876549,0,false,-48127877120,-48127877056⟩
    { al := (6783/32768), au := (212181/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨227599712256,227827613959⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206766234944,206766235008⟩ : DyadicInterval 40),(⟨-254869513216,-254869513152⟩ : DyadicInterval 40),(⟨738419443431,738419462761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207002140800,207002140864⟩ : DyadicInterval 40),(⟨-255228598016,-255228597952⟩ : DyadicInterval 40),(⟨738359629128,738359648457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29363450,58790768⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29363008,29363072⟩ : DyadicInterval 40),(⟨-29363904,-29363840⟩ : DyadicInterval 40),(⟨762123383215,762123402544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58789184,58789248⟩ : DyadicInterval 40),(⟨-58792384,-58792320⟩ : DyadicInterval 40),(⟨762123382008,762123401337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227542807014,227799144164⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206813375168,206813375232⟩ : DyadicInterval 40),(⟨-254941252288,-254941252224⟩ : DyadicInterval 40),(⟨738407498129,738407517459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207025739072,207025739136⟩ : DyadicInterval 40),(⟨-255264528896,-255264528832⟩ : DyadicInterval 40),(⟨738353640805,738353660135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48238789824,-48127877056⟩ : DyadicInterval 40),(⟨786187322144,786242797792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨206860522176,207049322560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255300439104,-255013009408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1290_ok : ecellOkT e1290 = true := by decide +kernel
theorem e1290_pos {a z : ℝ} (ha1 : ((6783/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((212181/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1290 e1290_ok ha1 ha2 hz1 hz2 hz

-- box ['423513/2048000', '6783/32768', '3999/4000', '1']  interval_lower 666267105/1099511627776
noncomputable def e1291 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1326883438329,0,true,206671689408,206671689472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨872139817223,0,false,-254725654912,-254725654848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1326826595376,0,true,206624585920,206624585984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨872196660176,0,false,-254653995072,-254653995008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540992218,0,true,29364032,29364096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482263334,0,false,-29364864,-29364800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626991,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1326855011210,0,true,206648133248,206648133312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨872168244342,0,false,-254689817280,-254689817216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111348577,0,true,206860529216,206860529280⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨871911906975,0,false,-255013020224,-255013020160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052398317102,0,false,-48152491008,-48152490944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052504381390,0,false,-48041684032,-48041683968⟩
    { al := (423513/2048000), au := (6783/32768), zl := (3999/4000), zu := 1,
      A := ⟨227371810553,227599712256⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206671689408,206671689472⟩ : DyadicInterval 40),(⟨-254725654912,-254725654848⟩ : DyadicInterval 40),(⟨738443390355,738443409684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206624585920,206624585984⟩ : DyadicInterval 40),(⟨-254653995072,-254653995008⟩ : DyadicInterval 40),(⟨738455315593,738455334922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29364442⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29364032,29364096⟩ : DyadicInterval 40),(⟨-29364864,-29364800⟩ : DyadicInterval 40),(⟨762123383183,762123402512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨227343383434,227599720801⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206648133248,206648133312⟩ : DyadicInterval 40),(⟨-254689817280,-254689817216⟩ : DyadicInterval 40),(⟨738449354531,738449373860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860529216,206860529280⟩ : DyadicInterval 40),(⟨-255013020224,-255013020160⟩ : DyadicInterval 40),(⟨738395545750,738395565080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48152491008,-48041683968⟩ : DyadicInterval 40),(⟨786144225600,786199648384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨206671689408,206860522240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255013009472,-254725654848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1291_ok : ecellOkT e1291 = true := by decide +kernel
theorem e1291_pos {a z : ℝ} (ha1 : ((423513/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6783/32768 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1291 e1291_ok ha1 ha2 hz1 hz2 hz

-- box ['6783/32768', '212181/1024000', '3999/4000', '1']  interval_lower 671662451/1099511627776
noncomputable def e1292 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111340032,0,true,206860522176,206860522240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871911915520,0,false,-255013009472,-255013009408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241735,0,true,207049322496,207049322560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013817,0,false,-255300439104,-255300439040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327054440103,0,true,206813379520,206813379584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871968815449,0,false,-254941259008,-254941258944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541023527,0,true,29395328,29395392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482232025,0,false,-29396160,-29396096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626990,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1327082884416,0,true,206836946432,206836946496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨871940371136,0,false,-254977126528,-254977126464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339250279,0,true,207049329536,207049329600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨871684005273,0,false,-255300449856,-255300449792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052303918221,0,false,-48251120320,-48251120256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052410100571,0,false,-48140180032,-48140179968⟩
    { al := (6783/32768), au := (212181/1024000), zl := (3999/4000), zu := 1,
      A := ⟨227599712256,227827613959⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860522176,206860522240⟩ : DyadicInterval 40),(⟨-255013009472,-255013009408⟩ : DyadicInterval 40),(⟨738395547531,738395566860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206813379520,206813379584⟩ : DyadicInterval 40),(⟨-254941259008,-254941258944⟩ : DyadicInterval 40),(⟨738407497052,738407516381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29395751⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29395328,29395392⟩ : DyadicInterval 40),(⟨-29396160,-29396096⟩ : DyadicInterval 40),(⟨762123383182,762123402511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨227571256640,227827622503⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206836946432,206836946496⟩ : DyadicInterval 40),(⟨-254977126528,-254977126464⟩ : DyadicInterval 40),(⟨738401523854,738401543184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049329536,207049329600⟩ : DyadicInterval 40),(⟨-255300449856,-255300449792⟩ : DyadicInterval 40),(⟨738347653564,738347672894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48251120320,-48140179968⟩ : DyadicInterval 40),(⟨786193473600,786248963040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨206860522176,207049322560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255300439104,-255013009408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1292_ok : ecellOkT e1292 = true := by decide +kernel
theorem e1292_pos {a z : ℝ} (ha1 : ((6783/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((212181/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1292 e1292_ok ha1 ha2 hz1 hz2 hz

-- box ['212181/1024000', '849573/4096000', '999/1000', '3997/4000']  interval_lower 340035677/549755813888
noncomputable def e1293 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241734,0,true,207049322496,207049322560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013818,0,false,-255300439104,-255300439040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143437,0,true,207238090368,207238090432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112115,0,false,-255587943872,-255587943808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327111414119,0,true,206860583552,206860583616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871911841433,0,false,-255013102912,-255013102848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327396101801,0,true,207096421952,207096422016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871627153751,0,false,-255372162752,-255372162688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599811139,0,true,88179776,88179840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423444413,0,false,-88186944,-88186880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629332402,0,true,117698304,117698368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393923150,0,false,-117710976,-117710912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615175,0,false,-12608,-12544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620704,0,false,-7104,-7040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327225323950,0,true,206954953728,206954953792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871797931602,0,false,-255156756608,-255156756544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327481632167,0,true,207167266368,207167266432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871541623385,0,false,-255480060032,-255480059968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052244894447,0,false,-48312793664,-48312793600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052351119315,0,false,-48201802816,-48201802752⟩
    { al := (212181/1024000), au := (849573/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨227827613958,228055515661⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206860583552,206860583616⟩ : DyadicInterval 40),(⟨-255013102912,-255013102848⟩ : DyadicInterval 40),(⟨738395531978,738395551307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207096421952,207096422016⟩ : DyadicInterval 40),(⟨-255372162752,-255372162688⟩ : DyadicInterval 40),(⟨738335698861,738335718191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88183363,117704626⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88179776,88179840⟩ : DyadicInterval 40),(⟨-88186944,-88186880⟩ : DyadicInterval 40),(⟨762123380063,762123399392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117698304,117698368⟩ : DyadicInterval 40),(⟨-117710976,-117710912⟩ : DyadicInterval 40),(⟨762123377287,762123396616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12608,-7040⟩ : DyadicInterval 40),(⟨762123387136,762123409184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227713696174,227970004391⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206954953728,206954953792⟩ : DyadicInterval 40),(⟨-255156756608,-255156756544⟩ : DyadicInterval 40),(⟨738371600696,738371620025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207167266368,207167266432⟩ : DyadicInterval 40),(⟨-255480060032,-255480059968⟩ : DyadicInterval 40),(⟨738317707784,738317727113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48312793664,-48201802752⟩ : DyadicInterval 40),(⟨786224284992,786279799712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207049322496,207238090432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255587943872,-255300439040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1293_ok : ecellOkT e1293 = true := by decide +kernel
theorem e1293_pos {a z : ℝ} (ha1 : ((212181/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((849573/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1293 e1293_ok ha1 ha2 hz1 hz2 hz

-- box ['849573/4096000', '425211/2048000', '999/1000', '3997/4000']  interval_lower 685519417/1099511627776
noncomputable def e1294 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143436,0,true,207238090368,207238090432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112116,0,false,-255587943872,-255587943808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045139,0,true,207426825920,207426825984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210413,0,false,-255875523904,-255875523840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339087920,0,true,207049195072,207049195136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871684167632,0,false,-255300245056,-255300244992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327623832577,0,true,207285040192,207285040256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871399422975,0,false,-255659470592,-255659470528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599905077,0,true,88273728,88273792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423350475,0,false,-88280896,-88280832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629457681,0,true,117823552,117823616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393797871,0,false,-117836224,-117836160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615148,0,false,-12672,-12608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620689,0,false,-7104,-7040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327453111702,0,true,207143643520,207143643584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871570143850,0,false,-255444080064,-255444080000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327709448410,0,true,207355943232,207355943296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871313807142,0,false,-255767504000,-255767503936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052150377538,0,false,-48411560704,-48411560640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052256720432,0,false,-48300436544,-48300436480⟩
    { al := (849573/4096000), au := (425211/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨228055515660,228283417363⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049195072,207049195136⟩ : DyadicInterval 40),(⟨-255300245056,-255300244992⟩ : DyadicInterval 40),(⟨738347687682,738347707011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207285040192,207285040256⟩ : DyadicInterval 40),(⟨-255659470592,-255659470528⟩ : DyadicInterval 40),(⟨738287780989,738287800319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88277301,117829905⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88273728,88273792⟩ : DyadicInterval 40),(⟨-88280896,-88280832⟩ : DyadicInterval 40),(⟨762123380048,762123399377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117823552,117823616⟩ : DyadicInterval 40),(⟨-117836224,-117836160⟩ : DyadicInterval 40),(⟨762123377260,762123396590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12672,-7040⟩ : DyadicInterval 40),(⟨762123387136,762123409216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227941483926,228197820634⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207143643520,207143643584⟩ : DyadicInterval 40),(⟨-255444080064,-255444080000⟩ : DyadicInterval 40),(⟨738323707754,738323727083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207355943232,207355943296⟩ : DyadicInterval 40),(⟨-255767504000,-255767503936⟩ : DyadicInterval 40),(⟨738269753433,738269772762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48411560704,-48300436480⟩ : DyadicInterval 40),(⟨786273601856,786329183232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207238090368,207426825984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255875523904,-255587943808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1294_ok : ecellOkT e1294 = true := by decide +kernel
theorem e1294_pos {a z : ℝ} (ha1 : ((849573/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((425211/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1294 e1294_ok ha1 ha2 hz1 hz2 hz

-- box ['212181/1024000', '849573/4096000', '3997/4000', '1999/2000']  interval_lower 84884349/137438953472
noncomputable def e1295 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241734,0,true,207049322496,207049322560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013818,0,false,-255300439104,-255300439040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143437,0,true,207238090368,207238090432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112115,0,false,-255587943872,-255587943808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327168371023,0,true,206907771328,206907771392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871854884529,0,false,-255084929920,-255084929856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327453115680,0,true,207143646784,207143646848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871570139872,0,false,-255444085056,-255444084992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570417075,0,true,58787712,58787776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452838477,0,false,-58790912,-58790848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599907028,0,true,88275648,88275712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423348524,0,false,-88282816,-88282752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620688,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624633,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327253801621,0,true,206978545216,206978545280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871769453931,0,false,-255192673216,-255192673152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327510138549,0,true,207190877056,207190877120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871513117003,0,false,-255516023488,-255516023424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052233072823,0,false,-48325146368,-48325146304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052339322875,0,false,-48214127936,-48214127872⟩
    { al := (212181/1024000), au := (849573/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨227827613958,228055515661⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206907771328,206907771392⟩ : DyadicInterval 40),(⟨-255084929920,-255084929856⟩ : DyadicInterval 40),(⟨738383567443,738383586772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207143646784,207143646848⟩ : DyadicInterval 40),(⟨-255444085056,-255444084992⟩ : DyadicInterval 40),(⟨738323706926,738323726255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58789299,88279252⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58787712,58787776⟩ : DyadicInterval 40),(⟨-58790912,-58790848⟩ : DyadicInterval 40),(⟨762123382008,762123401337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88275648,88275712⟩ : DyadicInterval 40),(⟨-88282816,-88282752⟩ : DyadicInterval 40),(⟨762123380047,762123399377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227742173845,227998510773⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206978545216,206978545280⟩ : DyadicInterval 40),(⟨-255192673216,-255192673152⟩ : DyadicInterval 40),(⟨738365615877,738365635207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207190877056,207190877120⟩ : DyadicInterval 40),(⟨-255516023488,-255516023424⟩ : DyadicInterval 40),(⟨738311710028,738311729357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48325146368,-48214127872⟩ : DyadicInterval 40),(⟨786230447552,786285976064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207049322496,207238090432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255587943872,-255300439040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1295_ok : ecellOkT e1295 = true := by decide +kernel
theorem e1295_pos {a z : ℝ} (ha1 : ((212181/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((849573/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1295 e1295_ok ha1 ha2 hz1 hz2 hz

-- box ['849573/4096000', '425211/2048000', '3997/4000', '1999/2000']  interval_lower 171129803/274877906944
noncomputable def e1296 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143436,0,true,207238090368,207238090432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112116,0,false,-255587943872,-255587943808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045139,0,true,207426825920,207426825984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210413,0,false,-255875523904,-255875523840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327396101799,0,true,207096421952,207096422016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871627153753,0,false,-255372162752,-255372162688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327680903431,0,true,207332304128,207332304192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871342352121,0,false,-255731483648,-255731483584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570479702,0,true,58850304,58850368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452775850,0,false,-58853504,-58853440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600000989,0,true,88369600,88369664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423254563,0,false,-88376768,-88376704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620673,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624626,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327481617855,0,true,207167254528,207167254592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871541637697,0,false,-255480041984,-255480041920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327737983275,0,true,207379573504,207379573568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871285272277,0,false,-255803512768,-255803512704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052138532277,0,false,-48423939264,-48423939200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052244900383,0,false,-48312787456,-48312787392⟩
    { al := (849573/4096000), au := (425211/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨228055515660,228283417363⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207096421952,207096422016⟩ : DyadicInterval 40),(⟨-255372162752,-255372162688⟩ : DyadicInterval 40),(⟨738335698862,738335718191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207332304128,207332304192⟩ : DyadicInterval 40),(⟨-255731483648,-255731483584⟩ : DyadicInterval 40),(⟨738275764728,738275784058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58851926,88373213⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58850304,58850368⟩ : DyadicInterval 40),(⟨-58853504,-58853440⟩ : DyadicInterval 40),(⟨762123382001,762123401331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88369600,88369664⟩ : DyadicInterval 40),(⟨-88376768,-88376704⟩ : DyadicInterval 40),(⟨762123380032,762123399362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227969990079,228226355499⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207167254528,207167254592⟩ : DyadicInterval 40),(⟨-255480041984,-255480041920⟩ : DyadicInterval 40),(⟨738317710789,738317730119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207379573504,207379573568⟩ : DyadicInterval 40),(⟨-255803512768,-255803512704⟩ : DyadicInterval 40),(⟨738263743462,738263762792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48423939264,-48312787392⟩ : DyadicInterval 40),(⟨786279777312,786335372512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207238090368,207426825984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255875523904,-255587943808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1296_ok : ecellOkT e1296 = true := by decide +kernel
theorem e1296_pos {a z : ℝ} (ha1 : ((849573/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((425211/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1296 e1296_ok ha1 ha2 hz1 hz2 hz

-- box ['425211/2048000', '851271/4096000', '999/1000', '3997/4000']  interval_lower 690988183/1099511627776
noncomputable def e1297 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045138,0,true,207426825920,207426825984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210414,0,false,-255875523904,-255875523840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946841,0,true,207615529024,207615529088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308711,0,false,-256163179136,-256163179072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327566761720,0,true,207237774272,207237774336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871456493832,0,false,-255587462272,-255587462208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327851563352,0,true,207473626112,207473626176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871171692200,0,false,-255946853568,-255946853504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599999033,0,true,88367680,88367744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423256519,0,false,-88374848,-88374784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629582983,0,true,117948864,117948928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393672569,0,false,-117961536,-117961472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615121,0,false,-12672,-12608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620674,0,false,-7104,-7040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327680899456,0,true,207332300864,207332300928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871342356096,0,false,-255731478656,-255731478592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327937264651,0,true,207544587776,207544587840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871085990901,0,false,-256055023104,-256055023040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052055766224,0,false,-48510435264,-48510435200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052162227166,0,false,-48399177728,-48399177664⟩
    { al := (425211/2048000), au := (851271/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨228283417362,228511319065⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207237774272,207237774336⟩ : DyadicInterval 40),(⟨-255587462272,-255587462208⟩ : DyadicInterval 40),(⟨738299794135,738299813464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207473626112,207473626176⟩ : DyadicInterval 40),(⟨-255946853568,-255946853504⟩ : DyadicInterval 40),(⟨738239813826,738239833156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88371257,117955207⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88367680,88367744⟩ : DyadicInterval 40),(⟨-88374848,-88374784⟩ : DyadicInterval 40),(⟨762123380033,762123399362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨117948864,117948928⟩ : DyadicInterval 40),(⟨-117961536,-117961472⟩ : DyadicInterval 40),(⟨762123377233,762123396563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12672,-7040⟩ : DyadicInterval 40),(⟨762123387136,762123409216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228169271680,228425636875⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207332300864,207332300928⟩ : DyadicInterval 40),(⟨-255731478656,-255731478592⟩ : DyadicInterval 40),(⟨738275765557,738275784887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207544587776,207544587840⟩ : DyadicInterval 40),(⟨-256055023104,-256055023040⟩ : DyadicInterval 40),(⟨738221749712,738221769041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48510435264,-48399177664⟩ : DyadicInterval 40),(⟨786322972448,786378620512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207426825920,207615529088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256163179136,-255875523840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1297_ok : ecellOkT e1297 = true := by decide +kernel
theorem e1297_pos {a z : ℝ} (ha1 : ((425211/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((851271/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1297 e1297_ok ha1 ha2 hz1 hz2 hz

-- box ['851271/4096000', '21303/102400', '999/1000', '3997/4000']  interval_lower 696478017/1099511627776
noncomputable def e1298 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946840,0,true,207615529024,207615529088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308712,0,false,-256163179136,-256163179072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848543,0,true,207804199744,207804199808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407009,0,false,-256450909632,-256450909568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327794435520,0,true,207426321088,207426321152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871228820032,0,false,-255874754560,-255874754496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328079294128,0,true,207662179712,207662179776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870943961424,0,false,-256234311680,-256234311616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600093008,0,true,88461632,88461696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423162544,0,false,-88468800,-88468736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629708310,0,true,118074176,118074240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393547242,0,false,-118086912,-118086848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615094,0,false,-12736,-12672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620659,0,false,-7168,-7104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327908687200,0,true,207520925824,207520925888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871114568352,0,false,-256018952320,-256018952256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328165080894,0,true,207733199936,207733200000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870858174658,0,false,-256342617408,-256342617344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051961060504,0,false,-48609417408,-48609417344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052067639522,0,false,-48498026496,-48498026432⟩
    { al := (851271/4096000), au := (21303/102400), zl := (999/1000), zu := (3997/4000),
      A := ⟨228511319064,228739220767⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593011,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426321088,207426321152⟩ : DyadicInterval 40),(⟨-255874754560,-255874754496⟩ : DyadicInterval 40),(⟨738251851362,738251870692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207662179712,207662179776⟩ : DyadicInterval 40),(⟨-256234311680,-256234311616⟩ : DyadicInterval 40),(⟨738191797358,738191816687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88465232,118080534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88461632,88461696⟩ : DyadicInterval 40),(⟨-88468800,-88468736⟩ : DyadicInterval 40),(⟨762123380017,762123399347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118074176,118074240⟩ : DyadicInterval 40),(⟨-118086912,-118086848⟩ : DyadicInterval 40),(⟨762123377238,762123396568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12736,-7104⟩ : DyadicInterval 40),(⟨762123387168,762123409248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228397059424,228653453118⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207520925824,207520925888⟩ : DyadicInterval 40),(⟨-256018952320,-256018952256⟩ : DyadicInterval 40),(⟨738227774032,738227793362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207733199936,207733200000⟩ : DyadicInterval 40),(⟨-256342617408,-256342617344⟩ : DyadicInterval 40),(⟨738173696670,738173716000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48609417408,-48498026432⟩ : DyadicInterval 40),(⟨786372396832,786428111584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207615529024,207804199808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256450909632,-256163179072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1298_ok : ecellOkT e1298 = true := by decide +kernel
theorem e1298_pos {a z : ℝ} (ha1 : ((851271/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21303/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1298 e1298_ok ha1 ha2 hz1 hz2 hz

-- box ['425211/2048000', '851271/4096000', '3997/4000', '1999/2000']  interval_lower 10781001/17179869184
noncomputable def e1299 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045138,0,true,207426825920,207426825984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210414,0,false,-255875523904,-255875523840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946841,0,true,207615529024,207615529088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308711,0,false,-256163179136,-256163179072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327623832574,0,true,207285040192,207285040256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871399422978,0,false,-255659470592,-255659470528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327908691182,0,true,207520929152,207520929216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871114564370,0,false,-256018957376,-256018957312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570542342,0,true,58912960,58913024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452713210,0,false,-58916160,-58916096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600094967,0,true,88463616,88463680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423160585,0,false,-88470784,-88470720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620657,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624620,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327709434093,0,true,207355931392,207355931456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871313821459,0,false,-255767485952,-255767485888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327965828005,0,true,207568237568,207568237632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871057427547,0,false,-256091077248,-256091077184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052043897300,0,false,-48522839680,-48522839616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052150383482,0,false,-48411554496,-48411554432⟩
    { al := (425211/2048000), au := (851271/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨228283417362,228511319065⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207285040192,207285040256⟩ : DyadicInterval 40),(⟨-255659470592,-255659470528⟩ : DyadicInterval 40),(⟨738287780990,738287800320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207520929152,207520929216⟩ : DyadicInterval 40),(⟨-256018957376,-256018957312⟩ : DyadicInterval 40),(⟨738227773186,738227792516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58914566,88467191⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58912960,58913024⟩ : DyadicInterval 40),(⟨-58916160,-58916096⟩ : DyadicInterval 40),(⟨762123381995,762123401324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88463616,88463680⟩ : DyadicInterval 40),(⟨-88470784,-88470720⟩ : DyadicInterval 40),(⟨762123380017,762123399347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228197806317,228454200229⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207355931392,207355931456⟩ : DyadicInterval 40),(⟨-255767485952,-255767485888⟩ : DyadicInterval 40),(⟨738269756446,738269775775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207568237568,207568237632⟩ : DyadicInterval 40),(⟨-256091077248,-256091077184⟩ : DyadicInterval 40),(⟨738215727563,738215746892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48522839680,-48411554432⟩ : DyadicInterval 40),(⟨786329160832,786384822720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207426825920,207615529088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256163179136,-255875523840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1299_ok : ecellOkT e1299 = true := by decide +kernel
theorem e1299_pos {a z : ℝ} (ha1 : ((425211/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((851271/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1299 e1299_ok ha1 ha2 hz1 hz2 hz

-- box ['851271/4096000', '21303/102400', '3997/4000', '1999/2000']  interval_lower 695470313/1099511627776
noncomputable def e1300 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946840,0,true,207615529024,207615529088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308712,0,false,-256163179136,-256163179072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848543,0,true,207804199744,207804199808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407009,0,false,-256450909632,-256450909568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327851563350,0,true,207473626112,207473626176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871171692202,0,false,-255946853568,-255946853504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328136478933,0,true,207709521792,207709521856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870886776619,0,false,-256306506240,-256306506176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570604992,0,true,58975616,58975680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452650560,0,false,-58978816,-58978752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600188964,0,true,88557568,88557632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423066588,0,false,-88564800,-88564736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620642,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624613,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327937250328,0,true,207544575936,207544576000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871086005224,0,false,-256055004992,-256055004928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328193672734,0,true,207756869248,207756869312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870829582818,0,false,-256378716928,-256378716864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051949167893,0,false,-48621847680,-48621847616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052055772176,0,false,-48510429056,-48510428992⟩
    { al := (851271/4096000), au := (21303/102400), zl := (3997/4000), zu := (1999/2000),
      A := ⟨228511319064,228739220767⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593011,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207473626112,207473626176⟩ : DyadicInterval 40),(⟨-255946853568,-255946853504⟩ : DyadicInterval 40),(⟨738239813826,738239833156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207709521792,207709521856⟩ : DyadicInterval 40),(⟨-256306506240,-256306506176⟩ : DyadicInterval 40),(⟨738179732326,738179751655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58977216,88561188⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58975616,58975680⟩ : DyadicInterval 40),(⟨-58978816,-58978752⟩ : DyadicInterval 40),(⟨762123381988,762123401317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88557568,88557632⟩ : DyadicInterval 40),(⟨-88564800,-88564736⟩ : DyadicInterval 40),(⟨762123380034,762123399364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228425622552,228682044958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207544575936,207544576000⟩ : DyadicInterval 40),(⟨-256055004992,-256055004928⟩ : DyadicInterval 40),(⟨738221752707,738221772036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207756869248,207756869312⟩ : DyadicInterval 40),(⟨-256378716928,-256378716864⟩ : DyadicInterval 40),(⟨738167662318,738167681647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48621847680,-48510428992⟩ : DyadicInterval 40),(⟨786378598112,786434326720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207615529024,207804199808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256450909632,-256163179072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1300_ok : ecellOkT e1300 = true := by decide +kernel
theorem e1300_pos {a z : ℝ} (ha1 : ((851271/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21303/102400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1300 e1300_ok ha1 ha2 hz1 hz2 hz

-- box ['212181/1024000', '849573/4096000', '1999/2000', '3999/4000']  interval_lower 339038617/549755813888
noncomputable def e1301 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241734,0,true,207049322496,207049322560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013818,0,false,-255300439104,-255300439040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143437,0,true,207238090368,207238090432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112115,0,false,-255587943872,-255587943808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327225327926,0,true,206954957056,206954957120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871797927626,0,false,-255156761600,-255156761536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327510129559,0,true,207190869632,207190869696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871513125993,0,false,-255516012160,-255516012096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541022535,0,true,29394304,29394368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482233017,0,false,-29395200,-29395136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570481174,0,true,58851776,58851840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452774378,0,false,-58854976,-58854912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624625,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626991,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327282279514,0,true,207002136384,207002136448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871740976038,0,false,-255228591296,-255228591232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327538645152,0,true,207214487424,207214487488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871484610400,0,false,-255551988352,-255551988288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052221249630,0,false,-48337500864,-48337500800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052327524869,0,false,-48226454912,-48226454848⟩
    { al := (212181/1024000), au := (849573/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨227827613958,228055515661⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206954957056,206954957120⟩ : DyadicInterval 40),(⟨-255156761600,-255156761536⟩ : DyadicInterval 40),(⟨738371599831,738371619160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207190869632,207190869696⟩ : DyadicInterval 40),(⟨-255516012160,-255516012096⟩ : DyadicInterval 40),(⟨738311711911,738311731241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29394759,58853398⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29394304,29394368⟩ : DyadicInterval 40),(⟨-29395200,-29395136⟩ : DyadicInterval 40),(⟨762123383214,762123402543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58851776,58851840⟩ : DyadicInterval 40),(⟨-58854976,-58854912⟩ : DyadicInterval 40),(⟨762123382001,762123401330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227770651738,228027017376⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207002136384,207002136448⟩ : DyadicInterval 40),(⟨-255228591296,-255228591232⟩ : DyadicInterval 40),(⟨738359630247,738359649576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207214487424,207214487488⟩ : DyadicInterval 40),(⟨-255551988352,-255551988288⟩ : DyadicInterval 40),(⟨738305711431,738305730761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48337500864,-48226454848⟩ : DyadicInterval 40),(⟨786236611040,786292153312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207049322496,207238090432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255587943872,-255300439040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1301_ok : ecellOkT e1301 = true := by decide +kernel
theorem e1301_pos {a z : ℝ} (ha1 : ((212181/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((849573/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1301 e1301_ok ha1 ha2 hz1 hz2 hz

-- box ['849573/4096000', '425211/2048000', '1999/2000', '3999/4000']  interval_lower 683517689/1099511627776
noncomputable def e1302 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143436,0,true,207238090368,207238090432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112116,0,false,-255587943872,-255587943808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045139,0,true,207426825920,207426825984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210413,0,false,-255875523904,-255875523840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327453115678,0,true,207143646784,207143646848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871570139874,0,false,-255444085056,-255444084992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327737974285,0,true,207379566016,207379566080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871285281267,0,false,-255803501440,-255803501376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541053849,0,true,29425664,29425728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482201703,0,false,-29426496,-29426432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570543817,0,true,58914432,58914496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452711735,0,false,-58917632,-58917568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624619,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626989,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327510124236,0,true,207190865216,207190865280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871513131316,0,false,-255516005440,-255516005376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327766518363,0,true,207403203392,207403203456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871256737189,0,false,-255839522944,-255839522880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052126685442,0,false,-48436319552,-48436319488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052233078760,0,false,-48325140160,-48325140096⟩
    { al := (849573/4096000), au := (425211/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨228055515660,228283417363⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207143646784,207143646848⟩ : DyadicInterval 40),(⟨-255444085056,-255444084992⟩ : DyadicInterval 40),(⟨738323706926,738323726255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207379566016,207379566080⟩ : DyadicInterval 40),(⟨-255803501440,-255803501376⟩ : DyadicInterval 40),(⟨738263745389,738263764718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29426073,58916041⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29425664,29425728⟩ : DyadicInterval 40),(⟨-29426496,-29426432⟩ : DyadicInterval 40),(⟨762123383180,762123402509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58914432,58914496⟩ : DyadicInterval 40),(⟨-58917632,-58917568⟩ : DyadicInterval 40),(⟨762123381994,762123401324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨227998496460,228254890587⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207190865216,207190865280⟩ : DyadicInterval 40),(⟨-255516005440,-255516005376⟩ : DyadicInterval 40),(⟨738311713034,738311732363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207403203392,207403203456⟩ : DyadicInterval 40),(⟨-255839522944,-255839522880⟩ : DyadicInterval 40),(⟨738257732686,738257752016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48436319552,-48325140096⟩ : DyadicInterval 40),(⟨786285953664,786341562656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207238090368,207426825984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255875523904,-255587943808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1302_ok : ecellOkT e1302 = true := by decide +kernel
theorem e1302_pos {a z : ℝ} (ha1 : ((849573/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((425211/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1302 e1302_ok ha1 ha2 hz1 hz2 hz

-- box ['212181/1024000', '849573/4096000', '3999/4000', '1']  interval_lower 169269717/274877906944
noncomputable def e1303 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327339241734,0,true,207049322496,207049322560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871684013818,0,false,-255300439104,-255300439040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143437,0,true,207238090368,207238090432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112115,0,false,-255587943872,-255587943808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327282284830,0,true,207002140800,207002140864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871740970722,0,false,-255228598016,-255228597952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541054843,0,true,29426624,29426688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482200709,0,false,-29427520,-29427456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626988,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1327310757631,0,true,207025727168,207025727232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨871712497921,0,false,-255264510848,-255264510784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567151977,0,true,207238097472,207238097536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨871456103575,0,false,-255587954688,-255587954624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052209424866,0,false,-48349857152,-48349857088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052315725294,0,false,-48238783616,-48238783552⟩
    { al := (212181/1024000), au := (849573/4096000), zl := (3999/4000), zu := 1,
      A := ⟨227827613958,228055515661⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207049322496,207049322560⟩ : DyadicInterval 40),(⟨-255300439104,-255300439040⟩ : DyadicInterval 40),(⟨738347655348,738347674678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207002140800,207002140864⟩ : DyadicInterval 40),(⟨-255228598016,-255228597952⟩ : DyadicInterval 40),(⟨738359629129,738359648458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29427067⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29426624,29426688⟩ : DyadicInterval 40),(⟨-29427520,-29427456⟩ : DyadicInterval 40),(⟨762123383212,762123402541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨227799129855,228055524201⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207025727168,207025727232⟩ : DyadicInterval 40),(⟨-255264510848,-255264510784⟩ : DyadicInterval 40),(⟨738353643844,738353663174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238097472,207238097536⟩ : DyadicInterval 40),(⟨-255587954688,-255587954624⟩ : DyadicInterval 40),(⟨738299712021,738299731350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48349857152,-48238783552⟩ : DyadicInterval 40),(⟨786242775392,786298331456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨207049322496,207238090432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255587943872,-255300439040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1303_ok : ecellOkT e1303 = true := by decide +kernel
theorem e1303_pos {a z : ℝ} (ha1 : ((212181/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((849573/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1303 e1303_ok ha1 ha2 hz1 hz2 hz

-- box ['849573/4096000', '425211/2048000', '3999/4000', '1']  interval_lower 170628927/274877906944
noncomputable def e1304 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327567143436,0,true,207238090368,207238090432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871456112116,0,false,-255587943872,-255587943808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045139,0,true,207426825920,207426825984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210413,0,false,-255875523904,-255875523840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327510129557,0,true,207190869632,207190869696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871513125995,0,false,-255516012160,-255516012096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541086165,0,true,29457984,29458048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482169387,0,false,-29458816,-29458752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626986,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1327538630838,0,true,207214475584,207214475648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨871484624714,0,false,-255551970304,-255551970240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795053681,0,true,207426832960,207426833024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨871228201871,0,false,-255875534656,-255875534592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052114837031,0,false,-48448701632,-48448701568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052221255568,0,false,-48337494720,-48337494656⟩
    { al := (849573/4096000), au := (425211/2048000), zl := (3999/4000), zu := 1,
      A := ⟨228055515660,228283417363⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207238090368,207238090432⟩ : DyadicInterval 40),(⟨-255587943872,-255587943808⟩ : DyadicInterval 40),(⟨738299713820,738299733150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207190869632,207190869696⟩ : DyadicInterval 40),(⟨-255516012160,-255516012096⟩ : DyadicInterval 40),(⟨738311711912,738311731241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29458389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29457984,29458048⟩ : DyadicInterval 40),(⟨-29458816,-29458752⟩ : DyadicInterval 40),(⟨762123383178,762123402507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨228027003062,228283425905⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207214475584,207214475648⟩ : DyadicInterval 40),(⟨-255551970304,-255551970240⟩ : DyadicInterval 40),(⟨738305714439,738305733768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426832960,207426833024⟩ : DyadicInterval 40),(⟨-255875534656,-255875534592⟩ : DyadicInterval 40),(⟨738251721116,738251740446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48448701632,-48337494656⟩ : DyadicInterval 40),(⟨786292130944,786347753696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨207238090368,207426825984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-255875523904,-255587943808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1304_ok : ecellOkT e1304 = true := by decide +kernel
theorem e1304_pos {a z : ℝ} (ha1 : ((849573/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((425211/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1304 e1304_ok ha1 ha2 hz1 hz2 hz

-- box ['425211/2048000', '851271/4096000', '1999/2000', '3999/4000']  interval_lower 688979145/1099511627776
noncomputable def e1305 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045138,0,true,207426825920,207426825984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210414,0,false,-255875523904,-255875523840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946841,0,true,207615529024,207615529088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308711,0,false,-256163179136,-256163179072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327680903429,0,true,207332304128,207332304192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871342352123,0,false,-255731483648,-255731483584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1327965819012,0,true,207568230080,207568230144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨871057436540,0,false,-256091065856,-256091065792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541085170,0,true,29456960,29457024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482170382,0,false,-29457792,-29457728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570606470,0,true,58977088,58977152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452649082,0,false,-58980288,-58980224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624612,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626987,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327737968958,0,true,207379561600,207379561664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871285286594,0,false,-255803494656,-255803494592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1327994391581,0,true,207591886976,207591887040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨871028863971,0,false,-256127132800,-256127132736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1052032026799,0,false,-48535245824,-48535245760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052138538222,0,false,-48423933056,-48423932992⟩
    { al := (425211/2048000), au := (851271/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨228283417362,228511319065⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207332304128,207332304192⟩ : DyadicInterval 40),(⟨-255731483648,-255731483584⟩ : DyadicInterval 40),(⟨738275764728,738275784058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207568230080,207568230144⟩ : DyadicInterval 40),(⟨-256091065856,-256091065792⟩ : DyadicInterval 40),(⟨738215729469,738215748798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29457394,58978694⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29456960,29457024⟩ : DyadicInterval 40),(⟨-29457792,-29457728⟩ : DyadicInterval 40),(⟨762123383178,762123402507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58977088,58977152⟩ : DyadicInterval 40),(⟨-58980288,-58980224⟩ : DyadicInterval 40),(⟨762123381988,762123401317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228226341182,228482763805⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207379561600,207379561664⟩ : DyadicInterval 40),(⟨-255803494656,-255803494592⟩ : DyadicInterval 40),(⟨738263746489,738263765818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207591886976,207591887040⟩ : DyadicInterval 40),(⟨-256127132800,-256127132736⟩ : DyadicInterval 40),(⟨738209704606,738209723935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48535245824,-48423932992⟩ : DyadicInterval 40),(⟨786335350112,786391025792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207426825920,207615529088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256163179136,-255875523840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1305_ok : ecellOkT e1305 = true := by decide +kernel
theorem e1305_pos {a z : ℝ} (ha1 : ((425211/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((851271/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1305 e1305_ok ha1 ha2 hz1 hz2 hz

-- box ['851271/4096000', '21303/102400', '1999/2000', '3999/4000']  interval_lower 86807679/137438953472
noncomputable def e1306 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946840,0,true,207615529024,207615529088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308712,0,false,-256163179136,-256163179072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848543,0,true,207804199744,207804199808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407009,0,false,-256450909632,-256450909568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327908691180,0,true,207520929152,207520929216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871114564372,0,false,-256018957376,-256018957312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328193663739,0,true,207756861760,207756861824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870829591813,0,false,-256378705600,-256378705536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541116496,0,true,29488320,29488384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482139056,0,false,-29489152,-29489088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570669137,0,true,59039744,59039808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452586415,0,false,-59043008,-59042944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624605,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626986,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1327965813682,0,true,207568225664,207568225728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨871057441870,0,false,-256091059136,-256091059072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328222264790,0,true,207780538176,207780538240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870800990762,0,false,-256414817920,-256414817856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051937273706,0,false,-48634279680,-48634279616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1052043903253,0,false,-48522833408,-48522833344⟩
    { al := (851271/4096000), au := (21303/102400), zl := (1999/2000), zu := (3999/4000),
      A := ⟨228511319064,228739220767⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593011,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207520929152,207520929216⟩ : DyadicInterval 40),(⟨-256018957376,-256018957312⟩ : DyadicInterval 40),(⟨738227773187,738227792516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207756861760,207756861824⟩ : DyadicInterval 40),(⟨-256378705600,-256378705536⟩ : DyadicInterval 40),(⟨738167664253,738167683582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29488720,59041361⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29488320,29488384⟩ : DyadicInterval 40),(⟨-29489152,-29489088⟩ : DyadicInterval 40),(⟨762123383177,762123402506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59039744,59039808⟩ : DyadicInterval 40),(⟨-59043008,-59042944⟩ : DyadicInterval 40),(⟨762123382013,762123401342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228454185906,228710637014⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207568225664,207568225728⟩ : DyadicInterval 40),(⟨-256091059136,-256091059072⟩ : DyadicInterval 40),(⟨738215730597,738215749927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207780538176,207780538240⟩ : DyadicInterval 40),(⟨-256414817920,-256414817856⟩ : DyadicInterval 40),(⟨738161627180,738161646509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48634279680,-48522833344⟩ : DyadicInterval 40),(⟨786384800288,786440542720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207615529024,207804199808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256450909632,-256163179072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1306_ok : ecellOkT e1306 = true := by decide +kernel
theorem e1306_pos {a z : ℝ} (ha1 : ((851271/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21303/102400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1306 e1306_ok ha1 ha2 hz1 hz2 hz

-- box ['425211/2048000', '851271/4096000', '3999/4000', '1']  interval_lower 687973331/1099511627776
noncomputable def e1307 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1327795045138,0,true,207426825920,207426825984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871228210414,0,false,-255875523904,-255875523840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946841,0,true,207615529024,207615529088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308711,0,false,-256163179136,-256163179072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327737974283,0,true,207379566016,207379566080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871285281269,0,false,-255803501376,-255803501312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541117492,0,true,29489280,29489344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482138060,0,false,-29490112,-29490048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626985,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1327766504048,0,true,207403191552,207403191616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨871256751504,0,false,-255839504896,-255839504832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022955381,0,true,207615536064,207615536128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨871000300171,0,false,-256163189888,-256163189824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1052020154721,0,false,-48547653760,-48547653696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052126691387,0,false,-48436313344,-48436313280⟩
    { al := (425211/2048000), au := (851271/4096000), zl := (3999/4000), zu := 1,
      A := ⟨228283417362,228511319065⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207426825920,207426825984⟩ : DyadicInterval 40),(⟨-255875523904,-255875523840⟩ : DyadicInterval 40),(⟨738251722907,738251742236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207379566016,207379566080⟩ : DyadicInterval 40),(⟨-255803501376,-255803501312⟩ : DyadicInterval 40),(⟨738263745363,738263764693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29489716⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29489280,29489344⟩ : DyadicInterval 40),(⟨-29490112,-29490048⟩ : DyadicInterval 40),(⟨762123383177,762123402506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨228254876272,228511327605⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207403191552,207403191616⟩ : DyadicInterval 40),(⟨-255839504896,-255839504832⟩ : DyadicInterval 40),(⟨738257735700,738257755030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615536064,207615536128⟩ : DyadicInterval 40),(⟨-256163189888,-256163189824⟩ : DyadicInterval 40),(⟨738203680852,738203700181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48547653760,-48436313280⟩ : DyadicInterval 40),(⟨786341540256,786397229760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨207426825920,207615529088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256163179136,-255875523840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1307_ok : ecellOkT e1307 = true := by decide +kernel
theorem e1307_pos {a z : ℝ} (ha1 : ((425211/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((851271/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1307 e1307_ok ha1 ha2 hz1 hz2 hz

-- box ['851271/4096000', '21303/102400', '3999/4000', '1']  interval_lower 693451791/1099511627776
noncomputable def e1308 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022946840,0,true,207615529024,207615529088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨871000308712,0,false,-256163179136,-256163179072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848543,0,true,207804199744,207804199808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407009,0,false,-256450909632,-256450909568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1327965819010,0,true,207568230080,207568230144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871057436542,0,false,-256091065856,-256091065792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541148826,0,true,29520640,29520704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482106726,0,false,-29521472,-29521408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626983,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1327994377257,0,true,207591875136,207591875200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨871028878295,0,false,-256127114752,-256127114688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250857081,0,true,207804206848,207804206912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨870772398471,0,false,-256450920384,-256450920320⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051925377934,0,false,-48646713536,-48646713472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1052032032753,0,false,-48535239616,-48535239552⟩
    { al := (851271/4096000), au := (21303/102400), zl := (3999/4000), zu := 1,
      A := ⟨228511319064,228739220767⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207615529024,207615529088⟩ : DyadicInterval 40),(⟨-256163179136,-256163179072⟩ : DyadicInterval 40),(⟨738203682646,738203701976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593011,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207568230080,207568230144⟩ : DyadicInterval 40),(⟨-256091065856,-256091065792⟩ : DyadicInterval 40),(⟨738215729469,738215748798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593011,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29521050⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29520640,29520704⟩ : DyadicInterval 40),(⟨-29521472,-29521408⟩ : DyadicInterval 40),(⟨762123383175,762123402504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨228482749481,228739229305⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207591875136,207591875200⟩ : DyadicInterval 40),(⟨-256127114752,-256127114688⟩ : DyadicInterval 40),(⟨738209707628,738209726957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804206848,207804206912⟩ : DyadicInterval 40),(⟨-256450920384,-256450920320⟩ : DyadicInterval 40),(⟨738155591176,738155610505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48646713536,-48535239552⟩ : DyadicInterval 40),(⟨786391003392,786446759648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨207615529024,207804199808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256450909632,-256163179072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1308_ok : ecellOkT e1308 = true := by decide +kernel
theorem e1308_pos {a z : ℝ} (ha1 : ((851271/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21303/102400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1308 e1308_ok ha1 ha2 hz1 hz2 hz

-- box ['21303/102400', '852969/4096000', '999/1000', '3997/4000']  interval_lower 350994327/549755813888
noncomputable def e1309 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848542,0,true,207804199744,207804199808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407010,0,false,-256450909632,-256450909568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750245,0,true,207992838144,207992838208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505307,0,false,-256738715456,-256738715392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328022109321,0,true,207614835648,207614835712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨871001146231,0,false,-256162121856,-256162121792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328307024904,0,true,207850700992,207850701056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870716230648,0,false,-256521844992,-256521844928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600187000,0,true,88555648,88555712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423068552,0,false,-88562816,-88562752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629833661,0,true,118199488,118199552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393421891,0,false,-118212288,-118212224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615067,0,false,-12736,-12672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620644,0,false,-7168,-7104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328136474957,0,true,207709518464,207709518528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870886780595,0,false,-256306501248,-256306501184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328392897139,0,true,207921779776,207921779840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870630358413,0,false,-256630286976,-256630286912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051866260376,0,false,-48708507136,-48708507072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051972957490,0,false,-48596982720,-48596982656⟩
    { al := (21303/102400), au := (852969/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨228739220766,228967122469⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593012,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207614835648,207614835712⟩ : DyadicInterval 40),(⟨-256162121856,-256162121792⟩ : DyadicInterval 40),(⟨738203859247,738203878577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207850700992,207850701056⟩ : DyadicInterval 40),(⟨-256521844992,-256521844928⟩ : DyadicInterval 40),(⟨738143731597,738143750926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88559224,118205885⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88555648,88555712⟩ : DyadicInterval 40),(⟨-88562816,-88562752⟩ : DyadicInterval 40),(⟨762123380002,762123399332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118199488,118199552⟩ : DyadicInterval 40),(⟨-118212288,-118212224⟩ : DyadicInterval 40),(⟨762123377243,762123396573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12736,-7104⟩ : DyadicInterval 40),(⟨762123387168,762123409248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228624847181,228881269363⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207709518464,207709518528⟩ : DyadicInterval 40),(⟨-256306501248,-256306501184⟩ : DyadicInterval 40),(⟨738179733198,738179752527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207921779776,207921779840⟩ : DyadicInterval 40),(⟨-256630286976,-256630286912⟩ : DyadicInterval 40),(⟨738125594282,738125613612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48708507136,-48596982656⟩ : DyadicInterval 40),(⟨786421874944,786477656448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207804199744,207992838208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256738715456,-256450909568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1309_ok : ecellOkT e1309 = true := by decide +kernel
theorem e1309_pos {a z : ℝ} (ha1 : ((21303/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((852969/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1309 e1309_ok ha1 ha2 hz1 hz2 hz

-- box ['852969/4096000', '426909/2048000', '999/1000', '3997/4000']  interval_lower 176880021/274877906944
noncomputable def e1310 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750244,0,true,207992838144,207992838208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505308,0,false,-256738715456,-256738715392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651948,0,true,208181444160,208181444224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603604,0,false,-257026596608,-257026596544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328249783121,0,true,207803317824,207803317888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870773472431,0,false,-256449564352,-256449564288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328534755681,0,true,208039189888,208039189952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870488499871,0,false,-256809453504,-256809453440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600281011,0,true,88649600,88649664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422974541,0,false,-88656832,-88656768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099629959036,0,true,118324864,118324928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393296516,0,false,-118337664,-118337600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615040,0,false,-12800,-12736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620628,0,false,-7168,-7104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328364262707,0,true,207898078784,207898078848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870658992845,0,false,-256594125376,-256594125312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328620713381,0,true,208110327232,208110327296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870402542171,0,false,-256918031808,-256918031744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051771365844,0,false,-48807704512,-48807704448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051878181079,0,false,-48696046528,-48696046464⟩
    { al := (852969/4096000), au := (426909/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨228967122468,229195024172⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207803317824,207803317888⟩ : DyadicInterval 40),(⟨-256449564352,-256449564288⟩ : DyadicInterval 40),(⟨738155817931,738155837261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208039189888,208039189952⟩ : DyadicInterval 40),(⟨-256809453504,-256809453440⟩ : DyadicInterval 40),(⟨738095616567,738095635897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88653235,118331260⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88649600,88649664⟩ : DyadicInterval 40),(⟨-88656832,-88656768⟩ : DyadicInterval 40),(⟨762123380019,762123399349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118324864,118324928⟩ : DyadicInterval 40),(⟨-118337664,-118337600⟩ : DyadicInterval 40),(⟨762123377216,762123396546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12800,-7104⟩ : DyadicInterval 40),(⟨762123387168,762123409280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228852634931,229109085605⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207898078784,207898078848⟩ : DyadicInterval 40),(⟨-256594125376,-256594125312⟩ : DyadicInterval 40),(⟨738131643019,738131662348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208110327232,208110327296⟩ : DyadicInterval 40),(⟨-256918031808,-256918031744⟩ : DyadicInterval 40),(⟨738077442573,738077461902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48807704512,-48696046464⟩ : DyadicInterval 40),(⟨786471406848,786527255136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207992838144,208181444224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257026596608,-256738715392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1310_ok : ecellOkT e1310 = true := by decide +kernel
theorem e1310_pos {a z : ℝ} (ha1 : ((852969/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((426909/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1310 e1310_ok ha1 ha2 hz1 hz2 hz

-- box ['21303/102400', '852969/4096000', '3997/4000', '1999/2000']  interval_lower 350488583/549755813888
noncomputable def e1311 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848542,0,true,207804199744,207804199808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407010,0,false,-256450909632,-256450909568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750245,0,true,207992838144,207992838208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505307,0,false,-256738715456,-256738715392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328079294126,0,true,207662179712,207662179776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870943961426,0,false,-256234311680,-256234311616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328364266684,0,true,207898082048,207898082112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870658988868,0,false,-256594130368,-256594130304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570667656,0,true,59038272,59038336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452587896,0,false,-59041472,-59041408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600282980,0,true,88651584,88651648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422972572,0,false,-88658816,-88658752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620627,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624606,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328165066566,0,true,207733188096,207733188160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870858188986,0,false,-256342599296,-256342599232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328421517460,0,true,207945468544,207945468608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870601738092,0,false,-256666431872,-256666431808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051854344058,0,false,-48720963328,-48720963264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051961066464,0,false,-48609411200,-48609411136⟩
    { al := (21303/102400), au := (852969/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨228739220766,228967122469⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593012,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207662179712,207662179776⟩ : DyadicInterval 40),(⟨-256234311680,-256234311616⟩ : DyadicInterval 40),(⟨738191797358,738191816688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207898082048,207898082112⟩ : DyadicInterval 40),(⟨-256594130368,-256594130304⟩ : DyadicInterval 40),(⟨738131642183,738131661513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59039880,88655204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59038272,59038336⟩ : DyadicInterval 40),(⟨-59041472,-59041408⟩ : DyadicInterval 40),(⟨762123381981,762123401310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88651584,88651648⟩ : DyadicInterval 40),(⟨-88658816,-88658752⟩ : DyadicInterval 40),(⟨762123380019,762123399348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228653438790,228909889684⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207733188096,207733188160⟩ : DyadicInterval 40),(⟨-256342599296,-256342599232⟩ : DyadicInterval 40),(⟨738173699672,738173719002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207945468544,207945468608⟩ : DyadicInterval 40),(⟨-256666431872,-256666431808⟩ : DyadicInterval 40),(⟨738119547739,738119567068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48720963328,-48609411136⟩ : DyadicInterval 40),(⟨786428089184,786483884544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207804199744,207992838208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256738715456,-256450909568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1311_ok : ecellOkT e1311 = true := by decide +kernel
theorem e1311_pos {a z : ℝ} (ha1 : ((21303/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((852969/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1311 e1311_ok ha1 ha2 hz1 hz2 hz

-- box ['852969/4096000', '426909/2048000', '3997/4000', '1999/2000']  interval_lower 706504845/1099511627776
noncomputable def e1312 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750244,0,true,207992838144,207992838208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505308,0,false,-256738715456,-256738715392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651948,0,true,208181444160,208181444224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603604,0,false,-257026596608,-257026596544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328307024902,0,true,207850700992,207850701056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870716230650,0,false,-256521844992,-256521844928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328592054437,0,true,208086610048,208086610112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870431201115,0,false,-256881829760,-256881829696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570730331,0,true,59100928,59100992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452525221,0,false,-59104192,-59104128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600377014,0,true,88745600,88745664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422878538,0,false,-88752832,-88752768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620612,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624600,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328392882807,0,true,207921767872,207921767936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870630372745,0,false,-256630268864,-256630268800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328649362195,0,true,208134035584,208134035648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870373893357,0,false,-256954222208,-256954222144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051759425790,0,false,-48820186560,-48820186496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051866266344,0,false,-48708500928,-48708500864⟩
    { al := (852969/4096000), au := (426909/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨228967122468,229195024172⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207850700992,207850701056⟩ : DyadicInterval 40),(⟨-256521844992,-256521844928⟩ : DyadicInterval 40),(⟨738143731597,738143750927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208086610048,208086610112⟩ : DyadicInterval 40),(⟨-256881829760,-256881829696⟩ : DyadicInterval 40),(⟨738083502669,738083521998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59102555,88749238⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59100928,59100992⟩ : DyadicInterval 40),(⟨-59104192,-59104128⟩ : DyadicInterval 40),(⟨762123382006,762123401336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88745600,88745664⟩ : DyadicInterval 40),(⟨-88752832,-88752768⟩ : DyadicInterval 40),(⟨762123380004,762123399333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228881255031,229137734419⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207921767872,207921767936⟩ : DyadicInterval 40),(⟨-256630268864,-256630268800⟩ : DyadicInterval 40),(⟨738125597329,738125616659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208134035584,208134035648⟩ : DyadicInterval 40),(⟨-256954222208,-256954222144⟩ : DyadicInterval 40),(⟨738071383784,738071403113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48820186560,-48708500864⟩ : DyadicInterval 40),(⟨786477634048,786533496160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207992838144,208181444224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257026596608,-256738715392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1312_ok : ecellOkT e1312 = true := by decide +kernel
theorem e1312_pos {a z : ℝ} (ha1 : ((852969/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((426909/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1312 e1312_ok ha1 ha2 hz1 hz2 hz

-- box ['426909/2048000', '854667/4096000', '999/1000', '3997/4000']  interval_lower 713072679/1099511627776
noncomputable def e1313 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651947,0,true,208181444160,208181444224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603605,0,false,-257026596608,-257026596544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553650,0,true,208370017792,208370017856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701902,0,false,-257314553216,-257314553152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328477456922,0,true,207991767744,207991767808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870545798630,0,false,-256737081984,-256737081920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328762486456,0,true,208227646528,208227646592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870260769096,0,false,-257097137216,-257097137152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600375039,0,true,88743680,88743744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422880513,0,false,-88750848,-88750784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630084434,0,true,118450240,118450304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393171118,0,false,-118463040,-118462976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615013,0,false,-12800,-12736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620613,0,false,-7168,-7104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328592050462,0,true,208086606720,208086606784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870431205090,0,false,-256881824768,-256881824704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328848529620,0,true,208298842368,208298842432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870174725932,0,false,-257205851904,-257205851840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051676376907,0,false,-48907009536,-48907009472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051783310283,0,false,-48795217984,-48795217920⟩
    { al := (426909/2048000), au := (854667/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨229195024171,229422925874⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207991767744,207991767808⟩ : DyadicInterval 40),(⟨-256737081984,-256737081920⟩ : DyadicInterval 40),(⟨738107727298,738107746627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208227646528,208227646592⟩ : DyadicInterval 40),(⟨-257097137216,-257097137152⟩ : DyadicInterval 40),(⟨738047452180,738047471510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88747263,118456658⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88743680,88743744⟩ : DyadicInterval 40),(⟨-88750848,-88750784⟩ : DyadicInterval 40),(⟨762123379972,762123399302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118450240,118450304⟩ : DyadicInterval 40),(⟨-118463040,-118462976⟩ : DyadicInterval 40),(⟨762123377189,762123396519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12800,-7104⟩ : DyadicInterval 40),(⟨762123387168,762123409280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229080422686,229336901844⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208086606720,208086606784⟩ : DyadicInterval 40),(⟨-256881824768,-256881824704⟩ : DyadicInterval 40),(⟨738083503544,738083522873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208298842368,208298842432⟩ : DyadicInterval 40),(⟨-257205851904,-257205851840⟩ : DyadicInterval 40),(⟨738029241491,738029260820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48907009536,-48795217920⟩ : DyadicInterval 40),(⟨786520992576,786576907648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208181444160,208370017856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257314553216,-257026596544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1313_ok : ecellOkT e1313 = true := by decide +kernel
theorem e1313_pos {a z : ℝ} (ha1 : ((426909/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((854667/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1313 e1313_ok ha1 ha2 hz1 hz2 hz

-- box ['854667/4096000', '213879/1024000', '999/1000', '3997/4000']  interval_lower 359323219/549755813888
noncomputable def e1314 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553649,0,true,208370017792,208370017856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701903,0,false,-257314553216,-257314553152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455352,0,true,208558559168,208558559232⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800200,0,false,-257602585216,-257602585152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328705130723,0,true,208180185344,208180185408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870318124829,0,false,-257024674816,-257024674752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328990217232,0,true,208416070848,208416070912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870033038320,0,false,-257384896256,-257384896192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600469087,0,true,88837696,88837760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422786465,0,false,-88844928,-88844864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630209858,0,true,118575680,118575744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099393045694,0,false,-118588480,-118588416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614986,0,false,-12800,-12736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620598,0,false,-7232,-7168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328819838209,0,true,208275102400,208275102464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870203417343,0,false,-257169599424,-257169599360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329076345866,0,true,208487325248,208487325312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869946909686,0,false,-257493747456,-257493747392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051581293561,0,false,-49006422208,-49006422144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051688345108,0,false,-48894497024,-48894496960⟩
    { al := (854667/4096000), au := (213879/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨229422925873,229650827576⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208180185344,208180185408⟩ : DyadicInterval 40),(⟨-257024674816,-257024674752⟩ : DyadicInterval 40),(⟨738059587397,738059606726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208416070848,208416070912⟩ : DyadicInterval 40),(⟨-257384896256,-257384896192⟩ : DyadicInterval 40),(⟨737999238511,737999257841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88841311,118582082⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88837696,88837760⟩ : DyadicInterval 40),(⟨-88844928,-88844864⟩ : DyadicInterval 40),(⟨762123379989,762123399318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118575680,118575744⟩ : DyadicInterval 40),(⟨-118588480,-118588416⟩ : DyadicInterval 40),(⟨762123377162,762123396492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12800,-7168⟩ : DyadicInterval 40),(⟨762123387200,762123409280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229308210433,229564718090⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208275102400,208275102464⟩ : DyadicInterval 40),(⟨-257169599424,-257169599360⟩ : DyadicInterval 40),(⟨738035314685,738035334014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208487325248,208487325312⟩ : DyadicInterval 40),(⟨-257493747456,-257493747392⟩ : DyadicInterval 40),(⟨737980991058,737981010388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49006422208,-48894496960⟩ : DyadicInterval 40),(⟨786570632096,786626613984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208370017792,208558559232⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257602585216,-257314553152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1314_ok : ecellOkT e1314 = true := by decide +kernel
theorem e1314_pos {a z : ℝ} (ha1 : ((854667/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((213879/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1314 e1314_ok ha1 ha2 hz1 hz2 hz

-- box ['426909/2048000', '854667/4096000', '3997/4000', '1999/2000']  interval_lower 356026815/549755813888
noncomputable def e1315 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651947,0,true,208181444160,208181444224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603605,0,false,-257026596608,-257026596544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553650,0,true,208370017792,208370017856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701902,0,false,-257314553216,-257314553152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328534755678,0,true,208039189888,208039189952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870488499874,0,false,-256809453504,-256809453440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328819842188,0,true,208275105664,208275105728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870203413364,0,false,-257169604416,-257169604352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570793018,0,true,59163648,59163712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452462534,0,false,-59166848,-59166784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600471066,0,true,88839680,88839744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422784486,0,false,-88846912,-88846848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620597,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624593,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328620699041,0,true,208110315392,208110315456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870402556511,0,false,-256918013632,-256918013568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328877206916,0,true,208322570240,208322570304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870146048636,0,false,-257242087808,-257242087744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051664413098,0,false,-48919517568,-48919517504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051771371821,0,false,-48807698240,-48807698176⟩
    { al := (426909/2048000), au := (854667/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨229195024171,229422925874⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208039189888,208039189952⟩ : DyadicInterval 40),(⟨-256809453504,-256809453440⟩ : DyadicInterval 40),(⟨738095616568,738095635898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208275105664,208275105728⟩ : DyadicInterval 40),(⟨-257169604416,-257169604352⟩ : DyadicInterval 40),(⟨738035313846,738035333175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59165242,88843290⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59163648,59163712⟩ : DyadicInterval 40),(⟨-59166848,-59166784⟩ : DyadicInterval 40),(⟨762123381968,762123401297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88839680,88839744⟩ : DyadicInterval 40),(⟨-88846912,-88846848⟩ : DyadicInterval 40),(⟨762123379988,762123399318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229109071265,229365579140⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208110315392,208110315456⟩ : DyadicInterval 40),(⟨-256918013632,-256918013568⟩ : DyadicInterval 40),(⟨738077445564,738077464894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208322570240,208322570304⟩ : DyadicInterval 40),(⟨-257242087808,-257242087744⟩ : DyadicInterval 40),(⟨738023170470,738023189799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48919517568,-48807698176⟩ : DyadicInterval 40),(⟨786527232704,786583161664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208181444160,208370017856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257314553216,-257026596544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1315_ok : ecellOkT e1315 = true := by decide +kernel
theorem e1315_pos {a z : ℝ} (ha1 : ((426909/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((854667/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1315 e1315_ok ha1 ha2 hz1 hz2 hz

-- box ['854667/4096000', '213879/1024000', '3997/4000', '1999/2000']  interval_lower 358811705/549755813888
noncomputable def e1316 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553649,0,true,208370017792,208370017856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701903,0,false,-257314553216,-257314553152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455352,0,true,208558559168,208558559232⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800200,0,false,-257602585216,-257602585152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328762486454,0,true,208227646528,208227646592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870260769098,0,false,-257097137216,-257097137152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329047629939,0,true,208463569024,208463569088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869975625613,0,false,-257457454464,-257457454400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570855718,0,true,59226304,59226368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452399834,0,false,-59229568,-59229504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600565135,0,true,88933760,88933824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422690417,0,false,-88940992,-88940928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620582,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624586,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328848515277,0,true,208298830528,208298830592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870174740275,0,false,-257205833792,-257205833728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329105051650,0,true,208511072576,208511072640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869918203902,0,false,-257530028800,-257530028736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051569305971,0,false,-49018956224,-49018956160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051676382891,0,false,-48907003264,-48907003200⟩
    { al := (854667/4096000), au := (213879/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨229422925873,229650827576⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208227646528,208227646592⟩ : DyadicInterval 40),(⟨-257097137216,-257097137152⟩ : DyadicInterval 40),(⟨738047452181,738047471510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208463569024,208463569088⟩ : DyadicInterval 40),(⟨-257457454464,-257457454400⟩ : DyadicInterval 40),(⟨737987075674,737987095004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59227942,88937359⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59226304,59226368⟩ : DyadicInterval 40),(⟨-59229568,-59229504⟩ : DyadicInterval 40),(⟨762123381993,762123401322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88933760,88933824⟩ : DyadicInterval 40),(⟨-88940992,-88940928⟩ : DyadicInterval 40),(⟨762123379973,762123399303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229336887501,229593423874⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208298830528,208298830592⟩ : DyadicInterval 40),(⟨-257205833792,-257205833728⟩ : DyadicInterval 40),(⟨738029244515,738029263844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208511072576,208511072640⟩ : DyadicInterval 40),(⟨-257530028800,-257530028736⟩ : DyadicInterval 40),(⟨737974907792,737974927121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49018956224,-48907003200⟩ : DyadicInterval 40),(⟨786576885216,786632880992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208370017792,208558559232⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257602585216,-257314553152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1316_ok : ecellOkT e1316 = true := by decide +kernel
theorem e1316_pos {a z : ℝ} (ha1 : ((854667/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((213879/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1316 e1316_ok ha1 ha2 hz1 hz2 hz

-- box ['21303/102400', '852969/4096000', '1999/2000', '3999/4000']  interval_lower 699964439/1099511627776
noncomputable def e1317 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848542,0,true,207804199744,207804199808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407010,0,false,-256450909632,-256450909568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750245,0,true,207992838144,207992838208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505307,0,false,-256738715456,-256738715392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328136478931,0,true,207709521792,207709521856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870886776621,0,false,-256306506240,-256306506176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328421508465,0,true,207945461120,207945461184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870601747087,0,false,-256666420544,-256666420480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541147828,0,true,29519616,29519680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482107724,0,false,-29520512,-29520448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570731815,0,true,59102400,59102464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452523737,0,false,-59105664,-59105600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624598,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626984,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328193658405,0,true,207756857344,207756857408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870829597147,0,false,-256378698816,-256378698752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328450138011,0,true,207969157056,207969157120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870573117541,0,false,-256702578304,-256702578240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051842426155,0,false,-48733421248,-48733421184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051949173855,0,false,-48621841408,-48621841344⟩
    { al := (21303/102400), au := (852969/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨228739220766,228967122469⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593012,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207709521792,207709521856⟩ : DyadicInterval 40),(⟨-256306506240,-256306506176⟩ : DyadicInterval 40),(⟨738179732326,738179751656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207945461120,207945461184⟩ : DyadicInterval 40),(⟨-256666420544,-256666420480⟩ : DyadicInterval 40),(⟨738119549639,738119568968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29520052,59104039⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29519616,29519680⟩ : DyadicInterval 40),(⟨-29520512,-29520448⟩ : DyadicInterval 40),(⟨762123383207,762123402536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59102400,59102464⟩ : DyadicInterval 40),(⟨-59105664,-59105600⟩ : DyadicInterval 40),(⟨762123382006,762123401335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228682030629,228938510235⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207756857344,207756857408⟩ : DyadicInterval 40),(⟨-256378698816,-256378698752⟩ : DyadicInterval 40),(⟨738167665359,738167684689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207969157056,207969157120⟩ : DyadicInterval 40),(⟨-256702578304,-256702578240⟩ : DyadicInterval 40),(⟨738113500352,738113519682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48733421248,-48621841344⟩ : DyadicInterval 40),(⟨786434304288,786490113504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207804199744,207992838208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256738715456,-256450909568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1317_ok : ecellOkT e1317 = true := by decide +kernel
theorem e1317_pos {a z : ℝ} (ha1 : ((21303/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((852969/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1317 e1317_ok ha1 ha2 hz1 hz2 hz

-- box ['852969/4096000', '426909/2048000', '1999/2000', '3999/4000']  interval_lower 705488493/1099511627776
noncomputable def e1318 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750244,0,true,207992838144,207992838208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505308,0,false,-256738715456,-256738715392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651948,0,true,208181444160,208181444224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603604,0,false,-257026596608,-257026596544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328364266682,0,true,207898082048,207898082112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870658988870,0,false,-256594130368,-256594130304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328649353193,0,true,208134028096,208134028160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870373902359,0,false,-256954210816,-256954210752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541179167,0,true,29550976,29551040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482076385,0,false,-29551808,-29551744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570794507,0,true,59165120,59165184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452461045,0,false,-59168384,-59168320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624592,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626982,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328421503127,0,true,207945456704,207945456768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870601752425,0,false,-256666413824,-256666413760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328678011228,0,true,208157743552,208157743616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870345244324,0,false,-256990414080,-256990414016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051747484152,0,false,-48832670464,-48832670400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051854350027,0,false,-48720957056,-48720956992⟩
    { al := (852969/4096000), au := (426909/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨228967122468,229195024172⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207898082048,207898082112⟩ : DyadicInterval 40),(⟨-256594130368,-256594130304⟩ : DyadicInterval 40),(⟨738131642184,738131661513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208134028096,208134028160⟩ : DyadicInterval 40),(⟨-256954210816,-256954210752⟩ : DyadicInterval 40),(⟨738071385703,738071405032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29551391,59166731⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29550976,29551040⟩ : DyadicInterval 40),(⟨-29551808,-29551744⟩ : DyadicInterval 40),(⟨762123383173,762123402502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59165120,59165184⟩ : DyadicInterval 40),(⟨-59168384,-59168320⟩ : DyadicInterval 40),(⟨762123382000,762123401329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨228909875351,229166383452⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207945456704,207945456768⟩ : DyadicInterval 40),(⟨-256666413824,-256666413760⟩ : DyadicInterval 40),(⟨738119550774,738119570103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208157743552,208157743616⟩ : DyadicInterval 40),(⟨-256990414080,-256990414016⟩ : DyadicInterval 40),(⟨738065324202,738065343531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48832670464,-48720956992⟩ : DyadicInterval 40),(⟨786483862112,786539738112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨207992838144,208181444224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257026596608,-256738715392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1318_ok : ecellOkT e1318 = true := by decide +kernel
theorem e1318_pos {a z : ℝ} (ha1 : ((852969/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((426909/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1318 e1318_ok ha1 ha2 hz1 hz2 hz

-- box ['21303/102400', '852969/4096000', '3999/4000', '1']  interval_lower 174737777/274877906944
noncomputable def e1319 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328250848542,0,true,207804199744,207804199808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870772407010,0,false,-256450909632,-256450909568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750245,0,true,207992838144,207992838208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505307,0,false,-256738715456,-256738715392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328193663736,0,true,207756861760,207756861824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870829591816,0,false,-256378705600,-256378705536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541180167,0,true,29551936,29552000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482075385,0,false,-29552832,-29552768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626981,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1328222250461,0,true,207780526336,207780526400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨870801005091,0,false,-256414799808,-256414799744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478758788,0,true,207992845184,207992845248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨870544496764,0,false,-256738726208,-256738726144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051830506667,0,false,-48745881024,-48745880960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051937279668,0,false,-48634273472,-48634273408⟩
    { al := (21303/102400), au := (852969/4096000), zl := (3999/4000), zu := 1,
      A := ⟨228739220766,228967122469⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207804199744,207804199808⟩ : DyadicInterval 40),(⟨-256450909632,-256450909568⟩ : DyadicInterval 40),(⟨738155593012,738155612341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207756861760,207756861824⟩ : DyadicInterval 40),(⟨-256378705600,-256378705536⟩ : DyadicInterval 40),(⟨738167664253,738167683583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29552391⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29551936,29552000⟩ : DyadicInterval 40),(⟨-29552832,-29552768⟩ : DyadicInterval 40),(⟨762123383205,762123402534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨228710622685,228967131012⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207780526336,207780526400⟩ : DyadicInterval 40),(⟨-256414799808,-256414799744⟩ : DyadicInterval 40),(⟨738161630184,738161649513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992845184,207992845248⟩ : DyadicInterval 40),(⟨-256738726208,-256738726144⟩ : DyadicInterval 40),(⟨738107452175,738107471504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48745881024,-48634273408⟩ : DyadicInterval 40),(⟨786440520320,786496343392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨207804199744,207992838208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-256738715456,-256450909568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1319_ok : ecellOkT e1319 = true := by decide +kernel
theorem e1319_pos {a z : ℝ} (ha1 : ((21303/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((852969/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1319 e1319_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B021

end


