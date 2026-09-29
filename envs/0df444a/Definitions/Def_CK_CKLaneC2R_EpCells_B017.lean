-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B017
-- name    : CK_CKLaneC2R_EpCells_B017
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:50.153663+00:00
-- url     : https://prove2.me/theorems/450583bf-dfcb-4e41-80c5-db7a4f92d4f0
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B017` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B017` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B017` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B017 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B017.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B017 =====
section

namespace CKLaneC2R.EpCells.B017

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['790143/4096000', '49437/256000', '3999/4000', '1']  interval_lower 2728387/8589934592
noncomputable def e1020 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024286,0,true,193945441984,193945442048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231266,0,false,-235641992832,-235641992768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925989,0,true,194136472896,194136472960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329563,0,false,-235924402304,-235924402240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311560998686,0,true,193900990336,193900990400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887462256866,0,false,-235576295360,-235576295296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538907805,0,true,27279680,27279744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484347747,0,false,-27280384,-27280320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627099,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1311587506153,0,true,193923211904,193923211968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨887435749399,0,false,-235609137024,-235609136960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841934504,0,true,194136480064,194136480128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨887181321048,0,false,-235924412800,-235924412736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058507823890,0,false,-41787932736,-41787932672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058606032007,0,false,-41685925056,-41685924992⟩
    { al := (790143/4096000), au := (49437/256000), zl := (3999/4000), zu := 1,
      A := ⟨212102396510,212330298213⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193900990336,193900990400⟩ : DyadicInterval 40),(⟨-235576295360,-235576295296⟩ : DyadicInterval 40),(⟨741547018262,741547037591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27280029⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27279680,27279744⟩ : DyadicInterval 40),(⟨-27280384,-27280320⟩ : DyadicInterval 40),(⟨762123383227,762123402556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨212075878377,212330306728⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193923211904,193923211968⟩ : DyadicInterval 40),(⟨-235609137024,-235609136960⟩ : DyadicInterval 40),(⟨741541840954,741541860283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136480064,194136480128⟩ : DyadicInterval 40),(⟨-235924412800,-235924412736⟩ : DyadicInterval 40),(⟨741492113175,741492132504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41787932736,-41685924992⟩ : DyadicInterval 40),(⟨782966346112,783017369248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨193945441984,194136472960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235924402304,-235641992768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1020_ok : ecellOkT e1020 = true := by decide +kernel
theorem e1020_pos {a z : ℝ} (ha1 : ((790143/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((49437/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1020 e1020_ok ha1 ha2 hz1 hz2 hz

-- box ['49437/256000', '791841/4096000', '999/1000', '3997/4000']  interval_lower 44458273/137438953472
noncomputable def e1021 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925988,0,true,194136472896,194136472960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329564,0,false,-235924402304,-235924402240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827691,0,true,194327470592,194327470656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427861,0,false,-236206884288,-236206884224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311629595689,0,true,193958495232,193958495296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887393659863,0,false,-235661286144,-235661286080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311910409042,0,true,194193870016,194193870080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887112846510,0,false,-236009278720,-236009278656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593464541,0,true,81833664,81833728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429791011,0,false,-81839872,-81839808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620868513,0,true,109235264,109235328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402387039,0,false,-109246208,-109246144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616922,0,false,-10880,-10816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621685,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311735756852,0,true,194047484352,194047484416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887287498700,0,false,-235792831424,-235792831360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311990127700,0,true,194260680192,194260680256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887033127852,0,false,-236108088640,-236108088576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058450567765,0,false,-41847408448,-41847408384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058548822269,0,false,-41745347008,-41745346944⟩
    { al := (49437/256000), au := (791841/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨212330298212,212558199915⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193958495232,193958495296⟩ : DyadicInterval 40),(⟨-235661286144,-235661286080⟩ : DyadicInterval 40),(⟨741533618814,741533638144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194193870016,194193870080⟩ : DyadicInterval 40),(⟨-236009278720,-236009278656⟩ : DyadicInterval 40),(⟨741478719479,741478738809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81836765,109240737⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81833664,81833728⟩ : DyadicInterval 40),(⟨-81839872,-81839808⟩ : DyadicInterval 40),(⟨762123380564,762123399894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109235264,109235328⟩ : DyadicInterval 40),(⟨-109246208,-109246144⟩ : DyadicInterval 40),(⟨762123378170,762123397499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10880,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123408320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212224129076,212478499924⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194047484352,194047484416⟩ : DyadicInterval 40),(⟨-235792831424,-235792831360⟩ : DyadicInterval 40),(⟨741512872939,741512892268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194260680192,194260680256⟩ : DyadicInterval 40),(⟨-236108088640,-236108088576⟩ : DyadicInterval 40),(⟨741463120809,741463140139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41847408448,-41745346944⟩ : DyadicInterval 40),(⟨782996057088,783047107104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194136472896,194327470656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236206884288,-235924402240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1021_ok : ecellOkT e1021 = true := by decide +kernel
theorem e1021_pos {a z : ℝ} (ha1 : ((49437/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((791841/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1021 e1021_ok ha1 ha2 hz1 hz2 hz

-- box ['791841/4096000', '79269/409600', '999/1000', '3997/4000']  interval_lower 359815639/1099511627776
noncomputable def e1022 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827690,0,true,194327470592,194327470656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427862,0,false,-236206884288,-236206884224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729393,0,true,194518435136,194518435200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526159,0,false,-236489438912,-236489438848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311857269490,0,true,194149332864,194149332928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887165986062,0,false,-235943418112,-235943418048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312138139817,0,true,194384714560,194384714624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886885115735,0,false,-236291570688,-236291570624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593557302,0,true,81926464,81926528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429698250,0,false,-81932608,-81932544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620992219,0,true,109358976,109359040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402263333,0,false,-109369920,-109369856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616897,0,false,-10880,-10816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621672,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311963544604,0,true,194238401984,194238402048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887059710948,0,false,-236075138368,-236075138304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312217943939,0,true,194451584704,194451584768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886805311613,0,false,-236390511872,-236390511808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058362470465,0,false,-41938927168,-41938927104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058460841388,0,false,-41836736320,-41836736256⟩
    { al := (791841/4096000), au := (79269/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨212558199914,212786101617⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194149332864,194149332928⟩ : DyadicInterval 40),(⟨-235943418112,-235943418048⟩ : DyadicInterval 40),(⟨741489114048,741489133377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194384714560,194384714624⟩ : DyadicInterval 40),(⟨-236291570688,-236291570624⟩ : DyadicInterval 40),(⟨741434143163,741434162492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81929526,109364443⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81926464,81926528⟩ : DyadicInterval 40),(⟨-81932608,-81932544⟩ : DyadicInterval 40),(⟨762123380518,762123399848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109358976,109359040⟩ : DyadicInterval 40),(⟨-109369920,-109369856⟩ : DyadicInterval 40),(⟨762123378145,762123397475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10880,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123408320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212451916828,212706316163⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194238401984,194238402048⟩ : DyadicInterval 40),(⟨-236075138368,-236075138304⟩ : DyadicInterval 40),(⟨741468323061,741468342391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194451584704,194451584768⟩ : DyadicInterval 40),(⟨-236390511872,-236390511808⟩ : DyadicInterval 40),(⟨741418510595,741418529925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41938927168,-41836736256⟩ : DyadicInterval 40),(⟨783041751744,783092866464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194327470592,194518435200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236489438912,-236206884224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1022_ok : ecellOkT e1022 = true := by decide +kernel
theorem e1022_pos {a z : ℝ} (ha1 : ((791841/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79269/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1022 e1022_ok ha1 ha2 hz1 hz2 hz

-- box ['49437/256000', '791841/4096000', '3997/4000', '1999/2000']  interval_lower 354897049/1099511627776
noncomputable def e1023 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925988,0,true,194136472896,194136472960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329564,0,false,-235924402304,-235924402240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827691,0,true,194327470592,194327470656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427861,0,false,-236206884288,-236206884224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311682678264,0,true,194002992384,194002992448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887340577288,0,false,-235727059264,-235727059200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311963548592,0,true,194238405376,194238405440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887059706960,0,false,-236075143296,-236075143232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566185915,0,true,54556736,54556800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457069637,0,false,-54559552,-54559488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593558967,0,true,81928128,81928192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429696585,0,false,-81934272,-81934208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621670,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625069,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311762297512,0,true,194069730816,194069730880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887260958040,0,false,-235825720640,-235825720576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312016697024,0,true,194282946304,194282946368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887006558528,0,false,-236141022848,-236141022784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058440298182,0,false,-41858076480,-41858076416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058538576046,0,false,-41755989824,-41755989760⟩
    { al := (49437/256000), au := (791841/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨212330298212,212558199915⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194002992384,194002992448⟩ : DyadicInterval 40),(⟨-235727059264,-235727059200⟩ : DyadicInterval 40),(⟨741523246797,741523266126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194238405376,194238405440⟩ : DyadicInterval 40),(⟨-236075143296,-236075143232⟩ : DyadicInterval 40),(⟨741468322245,741468341574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54558139,81931191⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54556736,54556800⟩ : DyadicInterval 40),(⟨-54559552,-54559488⟩ : DyadicInterval 40),(⟨762123382252,762123401581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81928128,81928192⟩ : DyadicInterval 40),(⟨-81934272,-81934208⟩ : DyadicInterval 40),(⟨762123380518,762123399848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212250669736,212505069248⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194069730816,194069730880⟩ : DyadicInterval 40),(⟨-235825720640,-235825720576⟩ : DyadicInterval 40),(⟨741507684725,741507704055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194282946304,194282946368⟩ : DyadicInterval 40),(⟨-236141022848,-236141022784⟩ : DyadicInterval 40),(⟨741457920656,741457939985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41858076480,-41755989760⟩ : DyadicInterval 40),(⟨783001378496,783052441120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194136472896,194327470656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236206884288,-235924402240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1023_ok : ecellOkT e1023 = true := by decide +kernel
theorem e1023_pos {a z : ℝ} (ha1 : ((49437/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((791841/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1023 e1023_ok ha1 ha2 hz1 hz2 hz

-- box ['791841/4096000', '79269/409600', '3997/4000', '1999/2000']  interval_lower 701257/2147483648
noncomputable def e1024 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827690,0,true,194327470592,194327470656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427862,0,false,-236206884288,-236206884224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729393,0,true,194518435136,194518435200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526159,0,false,-236489438912,-236489438848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311910409040,0,true,194193870016,194193870080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887112846512,0,false,-236009278720,-236009278656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312191336343,0,true,194429289856,194429289920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886831919209,0,false,-236357522752,-236357522688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566247757,0,true,54618624,54618688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457007795,0,false,-54621376,-54621312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593651749,0,true,82020864,82020928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429603803,0,false,-82027072,-82027008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621656,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625063,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311990113747,0,true,194260668480,194260668544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887033141805,0,false,-236108071360,-236108071296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312244541747,0,true,194473870848,194473870912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886778713805,0,false,-236423489856,-236423489792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058352178850,0,false,-41949618944,-41949618880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058450573159,0,false,-41847402816,-41847402752⟩
    { al := (791841/4096000), au := (79269/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨212558199914,212786101617⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194193870016,194193870080⟩ : DyadicInterval 40),(⟨-236009278720,-236009278656⟩ : DyadicInterval 40),(⟨741478719479,741478738809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194429289856,194429289920⟩ : DyadicInterval 40),(⟨-236357522752,-236357522688⟩ : DyadicInterval 40),(⟨741423723353,741423742682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54619981,82023973⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54618624,54618688⟩ : DyadicInterval 40),(⟨-54621376,-54621312⟩ : DyadicInterval 40),(⟨762123382214,762123401543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82020864,82020928⟩ : DyadicInterval 40),(⟨-82027072,-82027008⟩ : DyadicInterval 40),(⟨762123380536,762123399866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212478485971,212732913971⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194260668480,194260668544⟩ : DyadicInterval 40),(⟨-236108071360,-236108071296⟩ : DyadicInterval 40),(⟨741463123558,741463142887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194473870848,194473870912⟩ : DyadicInterval 40),(⟨-236423489856,-236423489792⟩ : DyadicInterval 40),(⟨741413299122,741413318451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41949618944,-41847402752⟩ : DyadicInterval 40),(⟨783047084992,783098212352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194327470592,194518435200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236489438912,-236206884224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1024_ok : ecellOkT e1024 = true := by decide +kernel
theorem e1024_pos {a z : ℝ} (ha1 : ((791841/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79269/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1024 e1024_ok ha1 ha2 hz1 hz2 hz

-- box ['79269/409600', '793539/4096000', '999/1000', '3997/4000']  interval_lower 2843613/8589934592
noncomputable def e1025 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729392,0,true,194518435136,194518435200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526160,0,false,-236489438912,-236489438848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631095,0,true,194709366528,194709366592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624457,0,false,-236772066112,-236772066048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312084943290,0,true,194340137408,194340137472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886938312262,0,false,-236225622464,-236225622400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312365870593,0,true,194575525952,194575526016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886657384959,0,false,-236573935040,-236573934976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593650080,0,true,82019200,82019264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429605472,0,false,-82025408,-82025344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621115947,0,true,109482688,109482752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402139605,0,false,-109493632,-109493568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616873,0,false,-10944,-10880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621658,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312191332358,0,true,194429286528,194429286592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886831923194,0,false,-236357517824,-236357517760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312445760186,0,true,194642456064,194642456128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886577495366,0,false,-236673007680,-236673007616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058274278756,0,false,-42030551616,-42030551552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058372766123,0,false,-41928231232,-41928231168⟩
    { al := (79269/409600), au := (793539/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨212786101616,213014003319⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194340137408,194340137472⟩ : DyadicInterval 40),(⟨-236225622464,-236225622400⟩ : DyadicInterval 40),(⟨741444560281,741444579611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194575525952,194575526016⟩ : DyadicInterval 40),(⟨-236573935040,-236573934976⟩ : DyadicInterval 40),(⟨741389517820,741389537150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82022304,109488171⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82019200,82019264⟩ : DyadicInterval 40),(⟨-82025408,-82025344⟩ : DyadicInterval 40),(⟨762123380537,762123399866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109482688,109482752⟩ : DyadicInterval 40),(⟨-109493632,-109493568⟩ : DyadicInterval 40),(⟨762123378120,762123397450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10944,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123408352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212679704582,212934132410⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194429286528,194429286592⟩ : DyadicInterval 40),(⟨-236357517824,-236357517760⟩ : DyadicInterval 40),(⟨741423724132,741423743461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194642456064,194642456128⟩ : DyadicInterval 40),(⟨-236673007680,-236673007616⟩ : DyadicInterval 40),(⟨741373851354,741373870683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42030551616,-41928231168⟩ : DyadicInterval 40),(⟨783087499200,783138678688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194518435136,194709366592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236772066112,-236489438848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1025_ok : ecellOkT e1025 = true := by decide +kernel
theorem e1025_pos {a z : ℝ} (ha1 : ((79269/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((793539/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1025 e1025_ok ha1 ha2 hz1 hz2 hz

-- box ['793539/4096000', '198597/1024000', '999/1000', '3997/4000']  interval_lower 368167245/1099511627776
noncomputable def e1026 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631094,0,true,194709366528,194709366592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624458,0,false,-236772066112,-236772066048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532797,0,true,194900264768,194900264832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722755,0,false,-237054766016,-237054765952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312312617090,0,true,194530908800,194530908864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886710638462,0,false,-236507899328,-236507899264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312593601369,0,true,194766304192,194766304256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886429654183,0,false,-236856372032,-236856371968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593742874,0,true,82112000,82112064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429512678,0,false,-82118208,-82118144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621239697,0,true,109606400,109606464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402015855,0,false,-109617408,-109617344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616848,0,false,-10944,-10880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621644,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312419120109,0,true,194620137920,194620137984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886604135443,0,false,-236639969856,-236639969792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312673576422,0,true,194833294336,194833294400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886349679130,0,false,-236955576128,-236955576064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058185992646,0,false,-42122281728,-42122281664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058284596478,0,false,-42019831872,-42019831808⟩
    { al := (793539/4096000), au := (198597/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨213014003318,213241905021⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194530908800,194530908864⟩ : DyadicInterval 40),(⟨-236507899328,-236507899264⟩ : DyadicInterval 40),(⟨741399957593,741399976922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194766304192,194766304256⟩ : DyadicInterval 40),(⟨-236856372032,-236856371968⟩ : DyadicInterval 40),(⟨741344843543,741344862873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82115098,109611921⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82112000,82112064⟩ : DyadicInterval 40),(⟨-82118208,-82118144⟩ : DyadicInterval 40),(⟨762123380523,762123399852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109606400,109606464⟩ : DyadicInterval 40),(⟨-109617408,-109617344⟩ : DyadicInterval 40),(⟨762123378128,762123397458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10944,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123408352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212907492333,213161948646⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194620137920,194620137984⟩ : DyadicInterval 40),(⟨-236639969856,-236639969792⟩ : DyadicInterval 40),(⟨741379076203,741379095533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194833294336,194833294400⟩ : DyadicInterval 40),(⟨-236955576128,-236955576064⟩ : DyadicInterval 40),(⟨741329143064,741329162393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42122281728,-42019831808⟩ : DyadicInterval 40),(⟨783133299520,783184543744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194709366528,194900264832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237054766016,-236772066048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1026_ok : ecellOkT e1026 = true := by decide +kernel
theorem e1026_pos {a z : ℝ} (ha1 : ((793539/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((198597/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1026 e1026_ok ha1 ha2 hz1 hz2 hz

-- box ['79269/409600', '793539/4096000', '3997/4000', '1999/2000']  interval_lower 363207525/1099511627776
noncomputable def e1027 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729392,0,true,194518435136,194518435200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526160,0,false,-236489438912,-236489438848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631095,0,true,194709366528,194709366592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624457,0,false,-236772066112,-236772066048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312138139815,0,true,194384714560,194384714624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886885115737,0,false,-236291570688,-236291570624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312419124094,0,true,194620141248,194620141312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886604131458,0,false,-236639974784,-236639974720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566309610,0,true,54680448,54680512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456945942,0,false,-54683200,-54683136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593744547,0,true,82113664,82113728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429511005,0,false,-82119872,-82119808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621643,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625057,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312217929981,0,true,194451572992,194451573056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886805325571,0,false,-236390494592,-236390494528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312472386477,0,true,194664762240,194664762304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886550869075,0,false,-236706029504,-236706029440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058263965085,0,false,-42041267200,-42041267136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058362475867,0,false,-41938921536,-41938921472⟩
    { al := (79269/409600), au := (793539/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨212786101616,213014003319⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194384714560,194384714624⟩ : DyadicInterval 40),(⟨-236291570688,-236291570624⟩ : DyadicInterval 40),(⟨741434143163,741434162492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194620141248,194620141312⟩ : DyadicInterval 40),(⟨-236639974784,-236639974720⟩ : DyadicInterval 40),(⟨741379075422,741379094752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54681834,82116771⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54680448,54680512⟩ : DyadicInterval 40),(⟨-54683200,-54683136⟩ : DyadicInterval 40),(⟨762123382208,762123401537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82113664,82113728⟩ : DyadicInterval 40),(⟨-82119872,-82119808⟩ : DyadicInterval 40),(⟨762123380522,762123399852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212706302205,212960758701⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194451572992,194451573056⟩ : DyadicInterval 40),(⟨-236390494592,-236390494528⟩ : DyadicInterval 40),(⟨741418513350,741418532680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194664762240,194664762304⟩ : DyadicInterval 40),(⟨-236706029504,-236706029440⟩ : DyadicInterval 40),(⟨741368628560,741368647890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42041267200,-41938921472⟩ : DyadicInterval 40),(⟨783092844352,783144036480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194518435136,194709366592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236772066112,-236489438848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1027_ok : ecellOkT e1027 = true := by decide +kernel
theorem e1027_pos {a z : ℝ} (ha1 : ((79269/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((793539/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1027 e1027_ok ha1 ha2 hz1 hz2 hz

-- box ['793539/4096000', '198597/1024000', '3997/4000', '1999/2000']  interval_lower 367389121/1099511627776
noncomputable def e1028 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631094,0,true,194709366528,194709366592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624458,0,false,-236772066112,-236772066048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532797,0,true,194900264768,194900264832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722755,0,false,-237054766016,-237054765952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312365870591,0,true,194575525952,194575526016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886657384961,0,false,-236573935040,-236573934976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312646911845,0,true,194810959552,194810959616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886376343707,0,false,-236922499392,-236922499328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566371474,0,true,54742272,54742336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456884078,0,false,-54745088,-54745024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593837362,0,true,82206464,82206528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429418190,0,false,-82212672,-82212608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621629,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625051,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312445746223,0,true,194642444416,194642444480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886577509329,0,false,-236672990400,-236672990336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312700231206,0,true,194855620480,194855620544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886323024346,0,false,-236988641728,-236988641664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058175656891,0,false,-42133021184,-42133021120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058274284166,0,false,-42030545984,-42030545920⟩
    { al := (793539/4096000), au := (198597/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨213014003318,213241905021⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194575525952,194575526016⟩ : DyadicInterval 40),(⟨-236573935040,-236573934976⟩ : DyadicInterval 40),(⟨741389517821,741389537150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194810959552,194810959616⟩ : DyadicInterval 40),(⟨-236922499392,-236922499328⟩ : DyadicInterval 40),(⟨741334378441,741334397771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54743698,82209586⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54742272,54742336⟩ : DyadicInterval 40),(⟨-54745088,-54745024⟩ : DyadicInterval 40),(⟨762123382234,762123401563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82206464,82206528⟩ : DyadicInterval 40),(⟨-82212672,-82212608⟩ : DyadicInterval 40),(⟨762123380509,762123399838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212934118447,213188603430⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194642444416,194642444480⟩ : DyadicInterval 40),(⟨-236672990400,-236672990336⟩ : DyadicInterval 40),(⟨741373854078,741373873407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194855620480,194855620544⟩ : DyadicInterval 40),(⟨-236988641728,-236988641664⟩ : DyadicInterval 40),(⟨741323908935,741323928265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42133021184,-42030545920⟩ : DyadicInterval 40),(⟨783138656576,783189913472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194709366528,194900264832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237054766016,-236772066048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1028_ok : ecellOkT e1028 = true := by decide +kernel
theorem e1028_pos {a z : ℝ} (ha1 : ((793539/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((198597/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1028 e1028_ok ha1 ha2 hz1 hz2 hz

-- box ['49437/256000', '791841/4096000', '1999/2000', '3999/4000']  interval_lower 88531797/274877906944
noncomputable def e1029 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925988,0,true,194136472896,194136472960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329564,0,false,-235924402304,-235924402240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827691,0,true,194327470592,194327470656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427861,0,false,-236206884288,-236206884224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311735760838,0,true,194047487680,194047487744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887287494714,0,false,-235792836352,-235792836288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312016688142,0,true,194282938880,194282938944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887006567410,0,false,-236141011840,-236141011776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538906908,0,true,27278784,27278848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484348644,0,false,-27279488,-27279424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566249039,0,true,54619904,54619968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457006513,0,false,-54622656,-54622592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625062,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627100,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311788838344,0,true,194091976960,194091977024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887234417208,0,false,-235858611072,-235858611008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312043266524,0,true,194305212160,194305212224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886979989028,0,false,-236173958208,-236173958144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058430027247,0,false,-41868745984,-41868745920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058528328475,0,false,-41766634112,-41766634048⟩
    { al := (49437/256000), au := (791841/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨212330298212,212558199915⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194047487680,194047487744⟩ : DyadicInterval 40),(⟨-235792836352,-235792836288⟩ : DyadicInterval 40),(⟨741512872163,741512891492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194282938880,194282938944⟩ : DyadicInterval 40),(⟨-236141011840,-236141011776⟩ : DyadicInterval 40),(⟨741457922383,741457941713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27279132,54621263⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27278784,27278848⟩ : DyadicInterval 40),(⟨-27279488,-27279424⟩ : DyadicInterval 40),(⟨762123383227,762123402556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54619904,54619968⟩ : DyadicInterval 40),(⟨-54622656,-54622592⟩ : DyadicInterval 40),(⟨762123382214,762123401543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212277210568,212531638748⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194091976960,194091977024⟩ : DyadicInterval 40),(⟨-235858611072,-235858611008⟩ : DyadicInterval 40),(⟨741502495830,741502515159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194305212160,194305212224⟩ : DyadicInterval 40),(⟨-236173958208,-236173958144⟩ : DyadicInterval 40),(⟨741452719751,741452739080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41868745984,-41766634048⟩ : DyadicInterval 40),(⟨783006700640,783057775872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194136472896,194327470656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236206884288,-235924402240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1029_ok : ecellOkT e1029 = true := by decide +kernel
theorem e1029_pos {a z : ℝ} (ha1 : ((49437/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((791841/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1029 e1029_ok ha1 ha2 hz1 hz2 hz

-- box ['791841/4096000', '79269/409600', '1999/2000', '3999/4000']  interval_lower 358270535/1099511627776
noncomputable def e1030 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827690,0,true,194327470592,194327470656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427862,0,false,-236206884288,-236206884224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729393,0,true,194518435136,194518435200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526159,0,false,-236489438912,-236489438848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311963548590,0,true,194238405376,194238405440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887059706962,0,false,-236075143296,-236075143232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312244532868,0,true,194473863424,194473863488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886778722684,0,false,-236423478848,-236423478784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538937829,0,true,27309696,27309760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484317723,0,false,-27310400,-27310336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566310895,0,true,54681728,54681792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456944657,0,false,-54684480,-54684416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625056,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627098,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312016683070,0,true,194282934656,194282934720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887006572482,0,false,-236141005568,-236141005504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312271139739,0,true,194496156736,194496156800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886752115813,0,false,-236456469056,-236456468992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058341885876,0,false,-41960312320,-41960312256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058440303577,0,false,-41858070848,-41858070784⟩
    { al := (791841/4096000), au := (79269/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨212558199914,212786101617⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194238405376,194238405440⟩ : DyadicInterval 40),(⟨-236075143296,-236075143232⟩ : DyadicInterval 40),(⟨741468322245,741468341575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194473863424,194473863488⟩ : DyadicInterval 40),(⟨-236423478848,-236423478784⟩ : DyadicInterval 40),(⟨741413300853,741413320182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27310053,54683119⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27309696,27309760⟩ : DyadicInterval 40),(⟨-27310400,-27310336⟩ : DyadicInterval 40),(⟨762123383225,762123402554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54681728,54681792⟩ : DyadicInterval 40),(⟨-54684480,-54684416⟩ : DyadicInterval 40),(⟨762123382208,762123401537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212505055294,212759511963⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194282934656,194282934720⟩ : DyadicInterval 40),(⟨-236141005568,-236141005504⟩ : DyadicInterval 40),(⟨741457923366,741457942696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194496156736,194496156800⟩ : DyadicInterval 40),(⟨-236456469056,-236456468992⟩ : DyadicInterval 40),(⟨741408086918,741408106248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41960312320,-41858070784⟩ : DyadicInterval 40),(⟨783052419008,783103559040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194327470592,194518435200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236489438912,-236206884224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1030_ok : ecellOkT e1030 = true := by decide +kernel
theorem e1030_pos {a z : ℝ} (ha1 : ((791841/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79269/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1030 e1030_ok ha1 ha2 hz1 hz2 hz

-- box ['49437/256000', '791841/4096000', '3999/4000', '1']  interval_lower 353356571/1099511627776
noncomputable def e1031 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925988,0,true,194136472896,194136472960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329564,0,false,-235924402304,-235924402240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827691,0,true,194327470592,194327470656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427861,0,false,-236206884288,-236206884224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311788843413,0,true,194091981184,194091981248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887234412139,0,false,-235858617344,-235858617280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538938727,0,true,27310592,27310656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484316825,0,false,-27311296,-27311232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627097,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1311815379360,0,true,194114222784,194114222848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨887207876192,0,false,-235891502720,-235891502656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069836206,0,true,194327477760,194327477824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨886953419346,0,false,-236206894848,-236206894784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058419754957,0,false,-41879417088,-41879417024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058518079552,0,false,-41777279872,-41777279808⟩
    { al := (49437/256000), au := (791841/4096000), zl := (3999/4000), zu := 1,
      A := ⟨212330298212,212558199915⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194091981184,194091981248⟩ : DyadicInterval 40),(⟨-235858617344,-235858617280⟩ : DyadicInterval 40),(⟨741502494849,741502514179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27310951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27310592,27310656⟩ : DyadicInterval 40),(⟨-27311296,-27311232⟩ : DyadicInterval 40),(⟨762123383225,762123402554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨212303751584,212558208430⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194114222784,194114222848⟩ : DyadicInterval 40),(⟨-235891502720,-235891502656⟩ : DyadicInterval 40),(⟨741497306248,741497325578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327477760,194327477824⟩ : DyadicInterval 40),(⟨-236206894848,-236206894784⟩ : DyadicInterval 40),(⟨741447518145,741447537475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41879417088,-41777279808⟩ : DyadicInterval 40),(⟨783012023520,783063111424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨194136472896,194327470656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236206884288,-235924402240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1031_ok : ecellOkT e1031 = true := by decide +kernel
theorem e1031_pos {a z : ℝ} (ha1 : ((49437/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((791841/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1031 e1031_ok ha1 ha2 hz1 hz2 hz

-- box ['791841/4096000', '79269/409600', '3999/4000', '1']  interval_lower 357497417/1099511627776
noncomputable def e1032 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312069827690,0,true,194327470592,194327470656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886953427862,0,false,-236206884288,-236206884224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729393,0,true,194518435136,194518435200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526159,0,false,-236489438912,-236489438848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312016688140,0,true,194282938880,194282938944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887006567412,0,false,-236141011840,-236141011776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538969656,0,true,27341504,27341568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484285896,0,false,-27342272,-27342208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627096,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1312043252569,0,true,194305200512,194305200576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨886980002983,0,false,-236173940928,-236173940864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297737907,0,true,194518442304,194518442368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨886725517645,0,false,-236489449472,-236489449408⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058331591548,0,false,-41971007104,-41971007040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058430032643,0,false,-41868740416,-41868740352⟩
    { al := (791841/4096000), au := (79269/409600), zl := (3999/4000), zu := 1,
      A := ⟨212558199914,212786101617⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194327470592,194327470656⟩ : DyadicInterval 40),(⟨-236206884288,-236206884224⟩ : DyadicInterval 40),(⟨741447519830,741447539160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194282938880,194282938944⟩ : DyadicInterval 40),(⟨-236141011840,-236141011776⟩ : DyadicInterval 40),(⟨741457922384,741457941713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27341880⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27341504,27341568⟩ : DyadicInterval 40),(⟨-27342272,-27342208⟩ : DyadicInterval 40),(⟨762123383256,762123402585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨212531624793,212786110131⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194305200512,194305200576⟩ : DyadicInterval 40),(⟨-236173940928,-236173940864⟩ : DyadicInterval 40),(⟨741452722463,741452741792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518442304,194518442368⟩ : DyadicInterval 40),(⟨-236489449472,-236489449408⟩ : DyadicInterval 40),(⟨741402874025,741402893354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41971007104,-41868740352⟩ : DyadicInterval 40),(⟨783057753792,783108906432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨194327470592,194518435200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236489438912,-236206884224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1032_ok : ecellOkT e1032 = true := by decide +kernel
theorem e1032_pos {a z : ℝ} (ha1 : ((791841/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79269/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1032 e1032_ok ha1 ha2 hz1 hz2 hz

-- box ['79269/409600', '793539/4096000', '1999/2000', '3999/4000']  interval_lower 362431483/1099511627776
noncomputable def e1033 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729392,0,true,194518435136,194518435200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526160,0,false,-236489438912,-236489438848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631095,0,true,194709366528,194709366592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624457,0,false,-236772066112,-236772066048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312191336341,0,true,194429289856,194429289920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886831919211,0,false,-236357522752,-236357522688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312472377595,0,true,194664754816,194664754880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886550877957,0,false,-236706018432,-236706018368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538968756,0,true,27340608,27340672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484286796,0,false,-27341376,-27341312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566372761,0,true,54743616,54743680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456882791,0,false,-54746368,-54746304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625050,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627097,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312244527788,0,true,194473859136,194473859200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886778727764,0,false,-236423472576,-236423472512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312499012958,0,true,194687068096,194687068160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886524242594,0,false,-236739052480,-236739052416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058253650051,0,false,-42051984320,-42051984256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058352184252,0,false,-41949613376,-41949613312⟩
    { al := (79269/409600), au := (793539/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨212786101616,213014003319⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194429289856,194429289920⟩ : DyadicInterval 40),(⟨-236357522752,-236357522688⟩ : DyadicInterval 40),(⟨741423723353,741423742683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194664754816,194664754880⟩ : DyadicInterval 40),(⟨-236706018432,-236706018368⟩ : DyadicInterval 40),(⟨741368630270,741368649599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27340980,54744985⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27340608,27340672⟩ : DyadicInterval 40),(⟨-27341376,-27341312⟩ : DyadicInterval 40),(⟨762123383256,762123402585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54743616,54743680⟩ : DyadicInterval 40),(⟨-54746368,-54746304⟩ : DyadicInterval 40),(⟨762123382202,762123401531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212732900012,212987385182⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194473859136,194473859200⟩ : DyadicInterval 40),(⟨-236423472576,-236423472512⟩ : DyadicInterval 40),(⟨741413301878,741413321207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194687068096,194687068160⟩ : DyadicInterval 40),(⟨-236739052480,-236739052416⟩ : DyadicInterval 40),(⟨741363405045,741363424375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42051984320,-41949613312⟩ : DyadicInterval 40),(⟨783098190272,783149395040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194518435136,194709366592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236772066112,-236489438848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1033_ok : ecellOkT e1033 = true := by decide +kernel
theorem e1033_pos {a z : ℝ} (ha1 : ((79269/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((793539/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1033 e1033_ok ha1 ha2 hz1 hz2 hz

-- box ['793539/4096000', '198597/1024000', '1999/2000', '3999/4000']  interval_lower 45826271/137438953472
noncomputable def e1034 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631094,0,true,194709366528,194709366592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624458,0,false,-236772066112,-236772066048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532797,0,true,194900264768,194900264832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722755,0,false,-237054766016,-237054765952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312419124092,0,true,194620141248,194620141312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886604131460,0,false,-236639974784,-236639974720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312700222321,0,true,194855613056,194855613120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886323033231,0,false,-236988630720,-236988630656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538999690,0,true,27371520,27371584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484255862,0,false,-27372288,-27372224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566434639,0,true,54805440,54805504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456820913,0,false,-54808256,-54808192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625044,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627095,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312472372512,0,true,194664750528,194664750592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886550883040,0,false,-236706012160,-236706012096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312726886169,0,true,194877946368,194877946432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886296369383,0,false,-237021708544,-237021708480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058165319776,0,false,-42143762176,-42143762112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058263970496,0,false,-42041261568,-42041261504⟩
    { al := (793539/4096000), au := (198597/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨213014003318,213241905021⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194620141248,194620141312⟩ : DyadicInterval 40),(⟨-236639974784,-236639974720⟩ : DyadicInterval 40),(⟨741379075423,741379094752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194855613056,194855613120⟩ : DyadicInterval 40),(⟨-236988630720,-236988630656⟩ : DyadicInterval 40),(⟨741323910675,741323930004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27371914,54806863⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27371520,27371584⟩ : DyadicInterval 40),(⟨-27372288,-27372224⟩ : DyadicInterval 40),(⟨762123383254,762123402583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54805440,54805504⟩ : DyadicInterval 40),(⟨-54808256,-54808192⟩ : DyadicInterval 40),(⟨762123382228,762123401557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212960744736,213215258393⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194664750528,194664750592⟩ : DyadicInterval 40),(⟨-236706012160,-236706012096⟩ : DyadicInterval 40),(⟨741368631298,741368650628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194877946368,194877946432⟩ : DyadicInterval 40),(⟨-237021708544,-237021708480⟩ : DyadicInterval 40),(⟨741318674071,741318693401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42143762176,-42041261504⟩ : DyadicInterval 40),(⟨783144014368,783195283968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194709366528,194900264832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237054766016,-236772066048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1034_ok : ecellOkT e1034 = true := by decide +kernel
theorem e1034_pos {a z : ℝ} (ha1 : ((793539/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((198597/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1034 e1034_ok ha1 ha2 hz1 hz2 hz

-- box ['79269/409600', '793539/4096000', '3999/4000', '1']  interval_lower 361655353/1099511627776
noncomputable def e1035 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312297729392,0,true,194518435136,194518435200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886725526160,0,false,-236489438912,-236489438848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631095,0,true,194709366528,194709366592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624457,0,false,-236772066112,-236772066048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312244532866,0,true,194473863424,194473863488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886778722686,0,false,-236423478848,-236423478784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539000591,0,true,27372416,27372480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484254961,0,false,-27373184,-27373120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627094,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1312271125779,0,true,194496145024,194496145088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨886752129773,0,false,-236456451712,-236456451648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525639614,0,true,194709373696,194709373760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨886497615938,0,false,-236772076672,-236772076608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058243333659,0,false,-42062702976,-42062702912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058341891280,0,false,-41960306688,-41960306624⟩
    { al := (79269/409600), au := (793539/4096000), zl := (3999/4000), zu := 1,
      A := ⟨212786101616,213014003319⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194518435136,194518435200⟩ : DyadicInterval 40),(⟨-236489438912,-236489438848⟩ : DyadicInterval 40),(⟨741402875713,741402895043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194473863424,194473863488⟩ : DyadicInterval 40),(⟨-236423478848,-236423478784⟩ : DyadicInterval 40),(⟨741413300853,741413320183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27372815⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27372416,27372480⟩ : DyadicInterval 40),(⟨-27373184,-27373120⟩ : DyadicInterval 40),(⟨762123383254,762123402583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨212759498003,213014011838⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194496145024,194496145088⟩ : DyadicInterval 40),(⟨-236456451712,-236456451648⟩ : DyadicInterval 40),(⟨741408089649,741408108979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709373696,194709373760⟩ : DyadicInterval 40),(⟨-236772076672,-236772076608⟩ : DyadicInterval 40),(⟨741358180799,741358200128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42062702976,-41960306624⟩ : DyadicInterval 40),(⟨783103536928,783154754368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨194518435136,194709366592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-236772066112,-236489438848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1035_ok : ecellOkT e1035 = true := by decide +kernel
theorem e1035_pos {a z : ℝ} (ha1 : ((79269/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((793539/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1035 e1035_ok ha1 ha2 hz1 hz2 hz

-- box ['793539/4096000', '198597/1024000', '3999/4000', '1']  interval_lower 365830617/1099511627776
noncomputable def e1036 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312525631094,0,true,194709366528,194709366592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886497624458,0,false,-236772066112,-236772066048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532797,0,true,194900264768,194900264832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722755,0,false,-237054766016,-237054765952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312472377593,0,true,194664754816,194664754880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886550877959,0,false,-236706018432,-236706018368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539031530,0,true,27403392,27403456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484224022,0,false,-27404096,-27404032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627093,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1312498998993,0,true,194687056384,194687056448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨886524256559,0,false,-236739035136,-236739035072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753541317,0,true,194900271872,194900271936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨886269714235,0,false,-237054776576,-237054776512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058154981295,0,false,-42154504640,-42154504576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058253655462,0,false,-42051978688,-42051978624⟩
    { al := (793539/4096000), au := (198597/1024000), zl := (3999/4000), zu := 1,
      A := ⟨213014003318,213241905021⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194709366528,194709366592⟩ : DyadicInterval 40),(⟨-236772066112,-236772066048⟩ : DyadicInterval 40),(⟨741358182492,741358201821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194664754816,194664754880⟩ : DyadicInterval 40),(⟨-236706018432,-236706018368⟩ : DyadicInterval 40),(⟨741368630270,741368649600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27403754⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27403392,27403456⟩ : DyadicInterval 40),(⟨-27404096,-27404032⟩ : DyadicInterval 40),(⟨762123383220,762123402550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨212987371217,213241913541⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194687056384,194687056448⟩ : DyadicInterval 40),(⟨-236739035136,-236739035072⟩ : DyadicInterval 40),(⟨741363407783,741363427113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900271872,194900271936⟩ : DyadicInterval 40),(⟨-237054776576,-237054776512⟩ : DyadicInterval 40),(⟨741313438548,741313457877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42154504640,-42051978624⟩ : DyadicInterval 40),(⟨783149372928,783200655200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨194709366528,194900264832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237054766016,-236772066048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1036_ok : ecellOkT e1036 = true := by decide +kernel
theorem e1036_pos {a z : ℝ} (ha1 : ((793539/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((198597/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1036 e1036_ok ha1 ha2 hz1 hz2 hz

-- box ['198597/1024000', '795237/4096000', '999/1000', '3997/4000']  interval_lower 372369433/1099511627776
noncomputable def e1037 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532796,0,true,194900264768,194900264832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722756,0,false,-237054766016,-237054765952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434500,0,true,195091129856,195091129920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821052,0,false,-237337538624,-237337538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312540290890,0,true,194721647104,194721647168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886482964662,0,false,-236790248640,-236790248576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312821332146,0,true,194957049408,194957049472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886201923406,0,false,-237138881536,-237138881472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593835685,0,true,82204800,82204864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429419867,0,false,-82211008,-82210944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621363470,0,true,109730176,109730240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401892082,0,false,-109741184,-109741120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616823,0,false,-11008,-10944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621630,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312646907860,0,true,194810956224,194810956288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886376347692,0,false,-236922494400,-236922494336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312901392666,0,true,195024099520,195024099584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886121862886,0,false,-237238217152,-237238217088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058097612126,0,false,-42214117632,-42214117568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058196332450,0,false,-42111538176,-42111538112⟩
    { al := (198597/1024000), au := (795237/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨213241905020,213469806724⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194721647104,194721647168⟩ : DyadicInterval 40),(⟨-236790248640,-236790248576⟩ : DyadicInterval 40),(⟨741355305906,741355325236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194957049408,194957049472⟩ : DyadicInterval 40),(⟨-237138881536,-237138881472⟩ : DyadicInterval 40),(⟨741300120192,741300139522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82207909,109735694⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82204800,82204864⟩ : DyadicInterval 40),(⟨-82211008,-82210944⟩ : DyadicInterval 40),(⟨762123380509,762123399838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109730176,109730240⟩ : DyadicInterval 40),(⟨-109741184,-109741120⟩ : DyadicInterval 40),(⟨762123378103,762123397433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11008,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123408384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213135280084,213389764890⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194810956224,194810956288⟩ : DyadicInterval 40),(⟨-236922494400,-236922494336⟩ : DyadicInterval 40),(⟨741334379198,741334398528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195024099520,195024099584⟩ : DyadicInterval 40),(⟨-237238217152,-237238217088⟩ : DyadicInterval 40),(⟨741284385684,741284405013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42214117632,-42111538112⟩ : DyadicInterval 40),(⟨783179152672,783230461696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194900264768,195091129920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237337538624,-237054765952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1037_ok : ecellOkT e1037 = true := by decide +kernel
theorem e1037_pos {a z : ℝ} (ha1 : ((198597/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((795237/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1037 e1037_ok ha1 ha2 hz1 hz2 hz

-- box ['795237/4096000', '398043/2048000', '999/1000', '3997/4000']  interval_lower 188294677/549755813888
noncomputable def e1038 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434499,0,true,195091129856,195091129920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821053,0,false,-237337538624,-237337538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336202,0,true,195281961792,195281961856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919350,0,false,-237620383936,-237620383872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312767964692,0,true,194912352320,194912352384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886255290860,0,false,-237072670464,-237072670400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313049062921,0,true,195147761536,195147761600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885974192631,0,false,-237421463616,-237421463552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593928512,0,true,82297600,82297664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429327040,0,false,-82303872,-82303808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621487264,0,true,109853952,109854016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401768288,0,false,-109865024,-109864960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616799,0,false,-11008,-10944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621616,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312874695612,0,true,195001741376,195001741440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886148559940,0,false,-237205091584,-237205091520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313129208912,0,true,195214871552,195214871616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885894046640,0,false,-237520930880,-237520930816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058009137199,0,false,-42306059328,-42306059264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058107974039,0,false,-42203350208,-42203350144⟩
    { al := (795237/4096000), au := (398043/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨213469806723,213697708426⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194912352320,194912352384⟩ : DyadicInterval 40),(⟨-237072670464,-237072670400⟩ : DyadicInterval 40),(⟨741310605234,741310624564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195147761536,195147761600⟩ : DyadicInterval 40),(⟨-237421463616,-237421463552⟩ : DyadicInterval 40),(⟨741255347818,741255367147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82300736,109859488⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82297600,82297664⟩ : DyadicInterval 40),(⟨-82303872,-82303808⟩ : DyadicInterval 40),(⟨762123380527,762123399856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109853952,109854016⟩ : DyadicInterval 40),(⟨-109865024,-109864960⟩ : DyadicInterval 40),(⟨762123378110,762123397440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11008,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123408384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213363067836,213617581136⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195001741376,195001741440⟩ : DyadicInterval 40),(⟨-237205091584,-237205091520⟩ : DyadicInterval 40),(⟨741289633194,741289652524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195214871552,195214871616⟩ : DyadicInterval 40),(⟨-237520930880,-237520930816⟩ : DyadicInterval 40),(⟨741239579292,741239598622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42306059328,-42203350144⟩ : DyadicInterval 40),(⟨783225058688,783276432544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195091129856,195281961856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237620383936,-237337538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1038_ok : ecellOkT e1038 = true := by decide +kernel
theorem e1038_pos {a z : ℝ} (ha1 : ((795237/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((398043/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1038 e1038_ok ha1 ha2 hz1 hz2 hz

-- box ['198597/1024000', '795237/4096000', '3997/4000', '1999/2000']  interval_lower 371588041/1099511627776
noncomputable def e1039 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532796,0,true,194900264768,194900264832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722756,0,false,-237054766016,-237054765952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434500,0,true,195091129856,195091129920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821052,0,false,-237337538624,-237337538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312593601367,0,true,194766304192,194766304256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886429654185,0,false,-236856372032,-236856371968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312874699597,0,true,195001744704,195001744768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886148555955,0,false,-237205096576,-237205096512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566433349,0,true,54804160,54804224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456822203,0,false,-54806976,-54806912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593930193,0,true,82299328,82299392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429325359,0,false,-82305536,-82305472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621615,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625045,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312673562453,0,true,194833282624,194833282688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886349693099,0,false,-236955558784,-236955558720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312928075934,0,true,195046445632,195046445696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886095179618,0,false,-237271326592,-237271326528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058087254268,0,false,-42224880960,-42224880896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058185998063,0,false,-42122276096,-42122276032⟩
    { al := (198597/1024000), au := (795237/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨213241905020,213469806724⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194766304192,194766304256⟩ : DyadicInterval 40),(⟨-236856372032,-236856371968⟩ : DyadicInterval 40),(⟨741344843544,741344862873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195001744704,195001744768⟩ : DyadicInterval 40),(⟨-237205096576,-237205096512⟩ : DyadicInterval 40),(⟨741289632436,741289651765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54805573,82302417⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54804160,54804224⟩ : DyadicInterval 40),(⟨-54806976,-54806912⟩ : DyadicInterval 40),(⟨762123382228,762123401557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82299328,82299392⟩ : DyadicInterval 40),(⟨-82305536,-82305472⟩ : DyadicInterval 40),(⟨762123380495,762123399824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213161934677,213416448158⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194833282624,194833282688⟩ : DyadicInterval 40),(⟨-236955558784,-236955558720⟩ : DyadicInterval 40),(⟨741329145808,741329165137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195046445632,195046445696⟩ : DyadicInterval 40),(⟨-237271326592,-237271326528⟩ : DyadicInterval 40),(⟨741279140222,741279159551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42224880960,-42122276032⟩ : DyadicInterval 40),(⟨783184521632,783235843360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194900264768,195091129920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237337538624,-237054765952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1039_ok : ecellOkT e1039 = true := by decide +kernel
theorem e1039_pos {a z : ℝ} (ha1 : ((198597/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((795237/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1039 e1039_ok ha1 ha2 hz1 hz2 hz

-- box ['795237/4096000', '398043/2048000', '3997/4000', '1999/2000']  interval_lower 375805161/1099511627776
noncomputable def e1040 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434499,0,true,195091129856,195091129920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821053,0,false,-237337538624,-237337538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336202,0,true,195281961792,195281961856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919350,0,false,-237620383936,-237620383872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312821332143,0,true,194957049408,194957049472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886201923409,0,false,-237138881536,-237138881472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313102487348,0,true,195192496768,195192496832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885920768204,0,false,-237487766400,-237487766336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566495236,0,true,54866048,54866112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456760316,0,false,-54868864,-54868800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594023041,0,true,82392128,82392192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429232511,0,false,-82398400,-82398336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621601,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625039,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312901378692,0,true,195024087808,195024087872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886121876860,0,false,-237238199808,-237238199744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313155920663,0,true,195237237632,195237237696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885867334889,0,false,-237554084224,-237554084160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057998757215,0,false,-42316846528,-42316846464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058097617551,0,false,-42214112000,-42214111936⟩
    { al := (795237/4096000), au := (398043/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨213469806723,213697708426⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194957049408,194957049472⟩ : DyadicInterval 40),(⟨-237138881536,-237138881472⟩ : DyadicInterval 40),(⟨741300120193,741300139522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195192496768,195192496832⟩ : DyadicInterval 40),(⟨-237487766400,-237487766336⟩ : DyadicInterval 40),(⟨741244837381,741244856711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54867460,82395265⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54866048,54866112⟩ : DyadicInterval 40),(⟨-54868864,-54868800⟩ : DyadicInterval 40),(⟨762123382221,762123401551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82392128,82392192⟩ : DyadicInterval 40),(⟨-82398400,-82398336⟩ : DyadicInterval 40),(⟨762123380513,762123399842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213389750916,213644292887⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195024087808,195024087872⟩ : DyadicInterval 40),(⟨-237238199808,-237238199744⟩ : DyadicInterval 40),(⟨741284388434,741284407764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195237237632,195237237696⟩ : DyadicInterval 40),(⟨-237554084224,-237554084160⟩ : DyadicInterval 40),(⟨741234322496,741234341825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42316846528,-42214111936⟩ : DyadicInterval 40),(⟨783230439584,783281826144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195091129856,195281961856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237620383936,-237337538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1040_ok : ecellOkT e1040 = true := by decide +kernel
theorem e1040_pos {a z : ℝ} (ha1 : ((795237/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((398043/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1040 e1040_ok ha1 ha2 hz1 hz2 hz

-- box ['398043/2048000', '159387/819200', '999/1000', '3997/4000']  interval_lower 190413363/549755813888
noncomputable def e1041 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336201,0,true,195281961792,195281961856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919351,0,false,-237620383936,-237620383872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237904,0,true,195472760640,195472760704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017648,0,false,-237903302080,-237903302016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312995638492,0,true,195103024448,195103024512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886027617060,0,false,-237355164864,-237355164800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313276793697,0,true,195338440576,195338440640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885746461855,0,false,-237704118400,-237704118336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594021355,0,true,82390464,82390528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429234197,0,false,-82396672,-82396608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621611081,0,true,109977792,109977856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401644471,0,false,-109988864,-109988800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616774,0,false,-11008,-10944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621602,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313102483360,0,true,195192493440,195192493504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885920772192,0,false,-237487761472,-237487761408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313357025152,0,true,195405610496,195405610560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885666230400,0,false,-237803717312,-237803717248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057920567869,0,false,-42398106816,-42398106752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058019521248,0,false,-42295267968,-42295267904⟩
    { al := (398043/2048000), au := (159387/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨213697708425,213925610128⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195103024448,195103024512⟩ : DyadicInterval 40),(⟨-237355164864,-237355164800⟩ : DyadicInterval 40),(⟨741265855592,741265874922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195338440576,195338440640⟩ : DyadicInterval 40),(⟨-237704118400,-237704118336⟩ : DyadicInterval 40),(⟨741210526460,741210545789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82393579,109983305⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82390464,82390528⟩ : DyadicInterval 40),(⟨-82396672,-82396608⟩ : DyadicInterval 40),(⟨762123380481,762123399810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109977792,109977856⟩ : DyadicInterval 40),(⟨-109988864,-109988800⟩ : DyadicInterval 40),(⟨762123378085,762123397415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11008,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123408384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213590855584,213845397376⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195192493440,195192493504⟩ : DyadicInterval 40),(⟨-237487761472,-237487761408⟩ : DyadicInterval 40),(⟨741244838168,741244857497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195405610496,195405610560⟩ : DyadicInterval 40),(⟨-237803717312,-237803717248⟩ : DyadicInterval 40),(⟨741194723840,741194743170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42398106816,-42295267904⟩ : DyadicInterval 40),(⟨783271017568,783322456288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195281961792,195472760704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237903302080,-237620383872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1041_ok : ecellOkT e1041 = true := by decide +kernel
theorem e1041_pos {a z : ℝ} (ha1 : ((398043/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159387/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1041 e1041_ok ha1 ha2 hz1 hz2 hz

-- box ['159387/819200', '99723/512000', '999/1000', '3997/4000']  interval_lower 385081943/1099511627776
noncomputable def e1042 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237903,0,true,195472760640,195472760704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017649,0,false,-237903302080,-237903302016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139606,0,true,195663526400,195663526464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115946,0,false,-238186292992,-238186292928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313223312292,0,true,195293663552,195293663616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885799943260,0,false,-237637731840,-237637731776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313504524473,0,true,195529086528,195529086592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885518731079,0,false,-237986845824,-237986845760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594114216,0,true,82483328,82483392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429141336,0,false,-82489536,-82489472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621734920,0,true,110101568,110101632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401520632,0,false,-110112704,-110112640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616749,0,false,-11072,-11008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621588,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313330271111,0,true,195383212416,195383212480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885692984441,0,false,-237770504000,-237770503936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313584841396,0,true,195596316352,195596316416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885438414156,0,false,-238086576512,-238086576448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057831904131,0,false,-42490260160,-42490260096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057930974073,0,false,-42387291520,-42387291456⟩
    { al := (159387/819200), au := (99723/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨213925610127,214153511830⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195293663552,195293663616⟩ : DyadicInterval 40),(⟨-237637731840,-237637731776⟩ : DyadicInterval 40),(⟨741221056928,741221076258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195529086528,195529086592⟩ : DyadicInterval 40),(⟨-237986845824,-237986845760⟩ : DyadicInterval 40),(⟨741165656080,741165675410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82486440,110107144⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82483328,82483392⟩ : DyadicInterval 40),(⟨-82489536,-82489472⟩ : DyadicInterval 40),(⟨762123380467,762123399797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110101568,110101632⟩ : DyadicInterval 40),(⟨-110112704,-110112640⟩ : DyadicInterval 40),(⟨762123378093,762123397423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11072,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123408416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213818643335,214073213620⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195383212416,195383212480⟩ : DyadicInterval 40),(⟨-237770504000,-237770503936⟩ : DyadicInterval 40),(⟨741199994080,741200013409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195596316352,195596316416⟩ : DyadicInterval 40),(⟨-238086576512,-238086576448⟩ : DyadicInterval 40),(⟨741149819339,741149838669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42490260160,-42387291456⟩ : DyadicInterval 40),(⟨783317029344,783368532960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195472760640,195663526464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238186292992,-237903302016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1042_ok : ecellOkT e1042 = true := by decide +kernel
theorem e1042_pos {a z : ℝ} (ha1 : ((159387/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((99723/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1042 e1042_ok ha1 ha2 hz1 hz2 hz

-- box ['398043/2048000', '159387/819200', '3997/4000', '1999/2000']  interval_lower 11876239/34359738368
noncomputable def e1043 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336201,0,true,195281961792,195281961856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919351,0,false,-237620383936,-237620383872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237904,0,true,195472760640,195472760704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017648,0,false,-237903302080,-237903302016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313049062919,0,true,195147761536,195147761600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885974192633,0,false,-237421463616,-237421463552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313330275100,0,true,195383215744,195383215808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885692980452,0,false,-237770508928,-237770508864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566557134,0,true,54927936,54928000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456698418,0,false,-54930752,-54930688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594115905,0,true,82484992,82485056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429139647,0,false,-82491264,-82491200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621587,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625032,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313129194932,0,true,195214859840,195214859904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885894060620,0,false,-237520913536,-237520913472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313383765391,0,true,195427996544,195427996608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885639490161,0,false,-237836914560,-237836914496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057910165733,0,false,-42408917952,-42408917888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058009142632,0,false,-42306053696,-42306053632⟩
    { al := (398043/2048000), au := (159387/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨213697708425,213925610128⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195147761536,195147761600⟩ : DyadicInterval 40),(⟨-237421463616,-237421463552⟩ : DyadicInterval 40),(⟨741255347818,741255367148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195383215744,195383215808⟩ : DyadicInterval 40),(⟨-237770508928,-237770508864⟩ : DyadicInterval 40),(⟨741199993291,741200012621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54929358,82488129⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54927936,54928000⟩ : DyadicInterval 40),(⟨-54930752,-54930688⟩ : DyadicInterval 40),(⟨762123382215,762123401544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82484992,82485056⟩ : DyadicInterval 40),(⟨-82491264,-82491200⟩ : DyadicInterval 40),(⟨762123380499,762123399828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213617567156,213872137615⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195214859840,195214859904⟩ : DyadicInterval 40),(⟨-237520913536,-237520913472⟩ : DyadicInterval 40),(⟨741239582050,741239601379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195427996544,195427996608⟩ : DyadicInterval 40),(⟨-237836914560,-237836914496⟩ : DyadicInterval 40),(⟨741189455683,741189475013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42408917952,-42306053632⟩ : DyadicInterval 40),(⟨783276410432,783327861856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195281961792,195472760704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237903302080,-237620383872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1043_ok : ecellOkT e1043 = true := by decide +kernel
theorem e1043_pos {a z : ℝ} (ha1 : ((398043/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159387/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1043 e1043_ok ha1 ha2 hz1 hz2 hz

-- box ['159387/819200', '99723/512000', '3997/4000', '1999/2000']  interval_lower 375285/1073741824
noncomputable def e1044 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237903,0,true,195472760640,195472760704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017649,0,false,-237903302080,-237903302016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139606,0,true,195663526400,195663526464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115946,0,false,-238186292992,-238186292928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313276793695,0,true,195338440576,195338440640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885746461857,0,false,-237704118400,-237704118336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313558062851,0,true,195573901632,195573901696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885465192701,0,false,-238053324224,-238053324160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566619041,0,true,54989888,54989952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456636511,0,false,-54992704,-54992640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594208786,0,true,82577856,82577920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429046766,0,false,-82584128,-82584064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621573,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625026,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313357011166,0,true,195405598784,195405598848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885666244386,0,false,-237803699968,-237803699904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313611610119,0,true,195618722368,195618722432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885411645433,0,false,-238119817664,-238119817600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057821479821,0,false,-42501095232,-42501095168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057920573310,0,false,-42398101184,-42398101120⟩
    { al := (159387/819200), au := (99723/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨213925610127,214153511830⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195338440576,195338440640⟩ : DyadicInterval 40),(⟨-237704118400,-237704118336⟩ : DyadicInterval 40),(⟨741210526460,741210545790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195573901632,195573901696⟩ : DyadicInterval 40),(⟨-238053324224,-238053324160⟩ : DyadicInterval 40),(⟨741155100179,741155119508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54991265,82581010⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54989888,54989952⟩ : DyadicInterval 40),(⟨-54992704,-54992640⟩ : DyadicInterval 40),(⟨762123382209,762123401538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82577856,82577920⟩ : DyadicInterval 40),(⟨-82584128,-82584064⟩ : DyadicInterval 40),(⟨762123380485,762123399814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213845383390,214099982343⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195405598784,195405598848⟩ : DyadicInterval 40),(⟨-237803699968,-237803699904⟩ : DyadicInterval 40),(⟨741194726605,741194745934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195618722368,195618722432⟩ : DyadicInterval 40),(⟨-238119817664,-238119817600⟩ : DyadicInterval 40),(⟨741144539796,741144559126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42501095232,-42398101120⟩ : DyadicInterval 40),(⟨783322434176,783373950496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195472760640,195663526464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238186292992,-237903302016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1044_ok : ecellOkT e1044 = true := by decide +kernel
theorem e1044_pos {a z : ℝ} (ha1 : ((159387/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((99723/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1044 e1044_ok ha1 ha2 hz1 hz2 hz

-- box ['198597/1024000', '795237/4096000', '1999/2000', '3999/4000']  interval_lower 92701615/274877906944
noncomputable def e1045 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532796,0,true,194900264768,194900264832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722756,0,false,-237054766016,-237054765952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434500,0,true,195091129856,195091129920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821052,0,false,-237337538624,-237337538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312646911843,0,true,194810959552,194810959616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886376343709,0,false,-236922499328,-236922499264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1312928067049,0,true,195046438208,195046438272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨886095188503,0,false,-237271315584,-237271315520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539030628,0,true,27402496,27402560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484224924,0,false,-27403200,-27403136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566496528,0,true,54867328,54867392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456759024,0,false,-54870144,-54870080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625037,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627094,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312700217240,0,true,194855608832,194855608896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886323038312,0,false,-236988624384,-236988624320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1312954759388,0,true,195068791488,195068791552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨886068496164,0,false,-237304437312,-237304437248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058076895044,0,false,-42235645824,-42235645760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058175662308,0,false,-42133015552,-42133015488⟩
    { al := (198597/1024000), au := (795237/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨213241905020,213469806724⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194810959552,194810959616⟩ : DyadicInterval 40),(⟨-236922499328,-236922499264⟩ : DyadicInterval 40),(⟨741334378416,741334397745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195046438208,195046438272⟩ : DyadicInterval 40),(⟨-237271315584,-237271315520⟩ : DyadicInterval 40),(⟨741279141965,741279161294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27402852,54868752⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27402496,27402560⟩ : DyadicInterval 40),(⟨-27403200,-27403136⟩ : DyadicInterval 40),(⟨762123383221,762123402550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54867328,54867392⟩ : DyadicInterval 40),(⟨-54870144,-54870080⟩ : DyadicInterval 40),(⟨762123382221,762123401550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213188589464,213443131612⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194855608832,194855608896⟩ : DyadicInterval 40),(⟨-236988624384,-236988624320⟩ : DyadicInterval 40),(⟨741323911641,741323930970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195068791488,195068791552⟩ : DyadicInterval 40),(⟨-237304437312,-237304437248⟩ : DyadicInterval 40),(⟨741273894045,741273913375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42235645824,-42133015488⟩ : DyadicInterval 40),(⟨783189891360,783241225792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨194900264768,195091129920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237337538624,-237054765952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1045_ok : ecellOkT e1045 = true := by decide +kernel
theorem e1045_pos {a z : ℝ} (ha1 : ((198597/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((795237/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1045 e1045_ok ha1 ha2 hz1 hz2 hz

-- box ['795237/4096000', '398043/2048000', '1999/2000', '3999/4000']  interval_lower 375020219/1099511627776
noncomputable def e1046 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434499,0,true,195091129856,195091129920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821053,0,false,-237337538624,-237337538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336202,0,true,195281961792,195281961856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919350,0,false,-237620383936,-237620383872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312874699595,0,true,195001744704,195001744768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886148555957,0,false,-237205096576,-237205096512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313155911776,0,true,195237230208,195237230272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885867343776,0,false,-237554073152,-237554073088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539061571,0,true,27433408,27433472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484193981,0,false,-27434176,-27434112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566558428,0,true,54929216,54929280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456697124,0,false,-54932032,-54931968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625031,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627092,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1312928061959,0,true,195046433920,195046433984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨886095193593,0,false,-237271309248,-237271309184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313182632603,0,true,195259603456,195259603520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885840622949,0,false,-237587238784,-237587238720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057988375860,0,false,-42327635264,-42327635200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058087259695,0,false,-42224875328,-42224875264⟩
    { al := (795237/4096000), au := (398043/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨213469806723,213697708426⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195001744704,195001744768⟩ : DyadicInterval 40),(⟨-237205096576,-237205096512⟩ : DyadicInterval 40),(⟨741289632436,741289651766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195237230208,195237230272⟩ : DyadicInterval 40),(⟨-237554073152,-237554073088⟩ : DyadicInterval 40),(⟨741234324218,741234343548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27433795,54930652⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27433408,27433472⟩ : DyadicInterval 40),(⟨-27434176,-27434112⟩ : DyadicInterval 40),(⟨762123383251,762123402580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54929216,54929280⟩ : DyadicInterval 40),(⟨-54932032,-54931968⟩ : DyadicInterval 40),(⟨762123382215,762123401544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213416434183,213671004827⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195046433920,195046433984⟩ : DyadicInterval 40),(⟨-237271309248,-237271309184⟩ : DyadicInterval 40),(⟨741279142973,741279162302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195259603456,195259603520⟩ : DyadicInterval 40),(⟨-237587238784,-237587238720⟩ : DyadicInterval 40),(⟨741229064957,741229084286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42327635264,-42224875264⟩ : DyadicInterval 40),(⟨783235821248,783287220512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195091129856,195281961856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237620383936,-237337538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1046_ok : ecellOkT e1046 = true := by decide +kernel
theorem e1046_pos {a z : ℝ} (ha1 : ((795237/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((398043/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1046 e1046_ok ha1 ha2 hz1 hz2 hz

-- box ['198597/1024000', '795237/4096000', '3999/4000', '1']  interval_lower 370024011/1099511627776
noncomputable def e1047 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312753532796,0,true,194900264768,194900264832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886269722756,0,false,-237054766016,-237054765952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434500,0,true,195091129856,195091129920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821052,0,false,-237337538624,-237337538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312700222319,0,true,194855613056,194855613120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886323033233,0,false,-236988630720,-236988630656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539062475,0,true,27434304,27434368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484193077,0,false,-27435072,-27435008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627091,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1312726872198,0,true,194877934656,194877934720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨886296383354,0,false,-237021691200,-237021691136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981443019,0,true,195091136960,195091137024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨886041812533,0,false,-237337549184,-237337549120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058066534455,0,false,-42246412160,-42246412096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058165325195,0,false,-42143756544,-42143756480⟩
    { al := (198597/1024000), au := (795237/4096000), zl := (3999/4000), zu := 1,
      A := ⟨213241905020,213469806724⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194900264768,194900264832⟩ : DyadicInterval 40),(⟨-237054766016,-237054765952⟩ : DyadicInterval 40),(⟨741313440206,741313459536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194855613056,194855613120⟩ : DyadicInterval 40),(⟨-236988630720,-236988630656⟩ : DyadicInterval 40),(⟨741323910675,741323930005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27434699⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27434304,27434368⟩ : DyadicInterval 40),(⟨-27435072,-27435008⟩ : DyadicInterval 40),(⟨762123383251,762123402580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨213215244422,213469815243⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194877934656,194877934720⟩ : DyadicInterval 40),(⟨-237021691200,-237021691136⟩ : DyadicInterval 40),(⟨741318676817,741318696146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091136960,195091137024⟩ : DyadicInterval 40),(⟨-237337549184,-237337549120⟩ : DyadicInterval 40),(⟨741268647182,741268666512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42246412160,-42143756480⟩ : DyadicInterval 40),(⟨783195261856,783246608960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨194900264768,195091129920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237337538624,-237054765952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1047_ok : ecellOkT e1047 = true := by decide +kernel
theorem e1047_pos {a z : ℝ} (ha1 : ((198597/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((795237/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1047 e1047_ok ha1 ha2 hz1 hz2 hz

-- box ['795237/4096000', '398043/2048000', '3999/4000', '1']  interval_lower 374234659/1099511627776
noncomputable def e1048 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1312981434499,0,true,195091129856,195091129920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨886041821053,0,false,-237337538624,-237337538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336202,0,true,195281961792,195281961856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919350,0,false,-237620383936,-237620383872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1312928067047,0,true,195046438208,195046438272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨886095188505,0,false,-237271315584,-237271315520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539093425,0,true,27465280,27465344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484162127,0,false,-27466048,-27465984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627089,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1312954745413,0,true,195068779776,195068779840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨886068510139,0,false,-237304419968,-237304419904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209344721,0,true,195281968960,195281969024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨885813910831,0,false,-237620394560,-237620394496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057977993138,0,false,-42338425536,-42338425472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058076900471,0,false,-42235640128,-42235640064⟩
    { al := (795237/4096000), au := (398043/2048000), zl := (3999/4000), zu := 1,
      A := ⟨213469806723,213697708426⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195091129856,195091129920⟩ : DyadicInterval 40),(⟨-237337538624,-237337538560⟩ : DyadicInterval 40),(⟨741268648844,741268668174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195046438208,195046438272⟩ : DyadicInterval 40),(⟨-237271315584,-237271315520⟩ : DyadicInterval 40),(⟨741279141965,741279161295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27465649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27465280,27465344⟩ : DyadicInterval 40),(⟨-27466048,-27465984⟩ : DyadicInterval 40),(⟨762123383249,762123402578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨213443117637,213697716945⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195068779776,195068779840⟩ : DyadicInterval 40),(⟨-237304419968,-237304419904⟩ : DyadicInterval 40),(⟨741273896797,741273916127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281968960,195281969024⟩ : DyadicInterval 40),(⟨-237620394560,-237620394496⟩ : DyadicInterval 40),(⟨741223806715,741223826044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42338425536,-42235640064⟩ : DyadicInterval 40),(⟨783241203648,783292615648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨195091129856,195281961856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237620383936,-237337538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1048_ok : ecellOkT e1048 = true := by decide +kernel
theorem e1048_pos {a z : ℝ} (ha1 : ((795237/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((398043/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1048 e1048_ok ha1 ha2 hz1 hz2 hz

-- box ['398043/2048000', '159387/819200', '1999/2000', '3999/4000']  interval_lower 379251531/1099511627776
noncomputable def e1049 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336201,0,true,195281961792,195281961856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919351,0,false,-237620383936,-237620383872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237904,0,true,195472760640,195472760704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017648,0,false,-237903302080,-237903302016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313102487346,0,true,195192496768,195192496832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885920768206,0,false,-237487766400,-237487766336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313383756502,0,true,195427989120,195427989184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885639499050,0,false,-237836903488,-237836903424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539092521,0,true,27464384,27464448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484163031,0,false,-27465152,-27465088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566620339,0,true,54991168,54991232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456635213,0,false,-54993984,-54993920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625025,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627090,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313155906682,0,true,195237225920,195237225984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885867348870,0,false,-237554066880,-237554066816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313410505816,0,true,195450382336,195450382400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885612749736,0,false,-237870112960,-237870112896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057899762225,0,false,-42419730624,-42419730560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057998762650,0,false,-42316840896,-42316840832⟩
    { al := (398043/2048000), au := (159387/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨213697708425,213925610128⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195192496768,195192496832⟩ : DyadicInterval 40),(⟨-237487766400,-237487766336⟩ : DyadicInterval 40),(⟨741244837382,741244856711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195427989120,195427989184⟩ : DyadicInterval 40),(⟨-237836903488,-237836903424⟩ : DyadicInterval 40),(⟨741189457410,741189476739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27464745,54992563⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27464384,27464448⟩ : DyadicInterval 40),(⟨-27465152,-27465088⟩ : DyadicInterval 40),(⟨762123383249,762123402578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54991168,54991232⟩ : DyadicInterval 40),(⟨-54993984,-54993920⟩ : DyadicInterval 40),(⟨762123382209,762123401538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213644278906,213898878040⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195237225920,195237225984⟩ : DyadicInterval 40),(⟨-237554066880,-237554066816⟩ : DyadicInterval 40),(⟨741234325255,741234344584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195450382336,195450382400⟩ : DyadicInterval 40),(⟨-237870112960,-237870112896⟩ : DyadicInterval 40),(⟨741184186755,741184206085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42419730624,-42316840832⟩ : DyadicInterval 40),(⟨783281804032,783333268192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195281961792,195472760704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237903302080,-237620383872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1049_ok : ecellOkT e1049 = true := by decide +kernel
theorem e1049_pos {a z : ℝ} (ha1 : ((398043/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159387/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1049 e1049_ok ha1 ha2 hz1 hz2 hz

-- box ['159387/819200', '99723/512000', '1999/2000', '3999/4000']  interval_lower 191750331/549755813888
noncomputable def e1050 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237903,0,true,195472760640,195472760704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017649,0,false,-237903302080,-237903302016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139606,0,true,195663526400,195663526464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115946,0,false,-238186292992,-238186292928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313330275097,0,true,195383215744,195383215808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885692980455,0,false,-237770508928,-237770508864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313611601229,0,true,195618714944,195618715008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885411654323,0,false,-238119806592,-238119806528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539123476,0,true,27495296,27495360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484132076,0,false,-27496064,-27496000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566682261,0,true,55053056,55053120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456573291,0,false,-55055872,-55055808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625019,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627089,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313383751405,0,true,195427984832,195427984896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885639504147,0,false,-237836897152,-237836897088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313638379033,0,true,195641128128,195641128192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885384876519,0,false,-238153060032,-238153059968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057811054134,0,false,-42511931840,-42511931776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057910171175,0,false,-42408912320,-42408912256⟩
    { al := (159387/819200), au := (99723/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨213925610127,214153511830⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195383215744,195383215808⟩ : DyadicInterval 40),(⟨-237770508928,-237770508864⟩ : DyadicInterval 40),(⟨741199993292,741200012621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195618714944,195618715008⟩ : DyadicInterval 40),(⟨-238119806592,-238119806528⟩ : DyadicInterval 40),(⟨741144541527,741144560856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27495700,55054485⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27495296,27495360⟩ : DyadicInterval 40),(⟨-27496064,-27496000⟩ : DyadicInterval 40),(⟨762123383248,762123402577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55053056,55053120⟩ : DyadicInterval 40),(⟨-55055872,-55055808⟩ : DyadicInterval 40),(⟨762123382203,762123401532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨213872123629,214126751257⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195427984832,195427984896⟩ : DyadicInterval 40),(⟨-237836897152,-237836897088⟩ : DyadicInterval 40),(⟨741189458423,741189477753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195641128128,195641128192⟩ : DyadicInterval 40),(⟨-238153060032,-238153059968⟩ : DyadicInterval 40),(⟨741139259504,741139278833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42511931840,-42408912256⟩ : DyadicInterval 40),(⟨783327839744,783379368800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195472760640,195663526464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238186292992,-237903302016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1050_ok : ecellOkT e1050 = true := by decide +kernel
theorem e1050_pos {a z : ℝ} (ha1 : ((159387/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((99723/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1050 e1050_ok ha1 ha2 hz1 hz2 hz

-- box ['398043/2048000', '159387/819200', '3999/4000', '1']  interval_lower 189231511/549755813888
noncomputable def e1051 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313209336201,0,true,195281961792,195281961856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885813919351,0,false,-237620383936,-237620383872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237904,0,true,195472760640,195472760704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017648,0,false,-237903302080,-237903302016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313155911773,0,true,195237230208,195237230272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885867343779,0,false,-237554073152,-237554073088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539124382,0,true,27496256,27496320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484131170,0,false,-27496960,-27496896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627088,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1313182618622,0,true,195259591744,195259591808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨885840636930,0,false,-237587221376,-237587221312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437246421,0,true,195472767808,195472767872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨885586009131,0,false,-237903312640,-237903312576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057889357345,0,false,-42430544832,-42430544768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057988381295,0,false,-42327629632,-42327629568⟩
    { al := (398043/2048000), au := (159387/819200), zl := (3999/4000), zu := 1,
      A := ⟨213697708425,213925610128⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195281961792,195281961856⟩ : DyadicInterval 40),(⟨-237620383936,-237620383872⟩ : DyadicInterval 40),(⟨741223808393,741223827722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195237230208,195237230272⟩ : DyadicInterval 40),(⟨-237554073152,-237554073088⟩ : DyadicInterval 40),(⟨741234324219,741234343548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27496606⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27496256,27496320⟩ : DyadicInterval 40),(⟨-27496960,-27496896⟩ : DyadicInterval 40),(⟨762123383216,762123402545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨213670990846,213925618645⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195259591744,195259591808⟩ : DyadicInterval 40),(⟨-237587221376,-237587221312⟩ : DyadicInterval 40),(⟨741229067690,741229087020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472767808,195472767872⟩ : DyadicInterval 40),(⟨-237903312640,-237903312576⟩ : DyadicInterval 40),(⟨741178917146,741178936476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42430544832,-42327629568⟩ : DyadicInterval 40),(⟨783287198400,783338675296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨195281961792,195472760704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-237903302080,-237620383872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1051_ok : ecellOkT e1051 = true := by decide +kernel
theorem e1051_pos {a z : ℝ} (ha1 : ((398043/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159387/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1051 e1051_ok ha1 ha2 hz1 hz2 hz

-- box ['159387/819200', '99723/512000', '3999/4000', '1']  interval_lower 47838651/137438953472
noncomputable def e1052 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313437237903,0,true,195472760640,195472760704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885586017649,0,false,-237903302080,-237903302016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139606,0,true,195663526400,195663526464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115946,0,false,-238186292992,-238186292928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313383756500,0,true,195427989120,195427989184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885639499052,0,false,-237836903488,-237836903424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539155343,0,true,27527168,27527232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484100209,0,false,-27527936,-27527872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627086,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1313410491829,0,true,195450370624,195450370688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨885612763723,0,false,-237870095616,-237870095552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665148128,0,true,195663533568,195663533632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨885358107424,0,false,-238186303616,-238186303552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057800627072,0,false,-42522770048,-42522769984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057899767668,0,false,-42419724992,-42419724928⟩
    { al := (159387/819200), au := (99723/512000), zl := (3999/4000), zu := 1,
      A := ⟨213925610127,214153511830⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195472760640,195472760704⟩ : DyadicInterval 40),(⟨-237903302080,-237903302016⟩ : DyadicInterval 40),(⟨741178918853,741178938183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195427989120,195427989184⟩ : DyadicInterval 40),(⟨-237836903488,-237836903424⟩ : DyadicInterval 40),(⟨741189457410,741189476739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27527567⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27527168,27527232⟩ : DyadicInterval 40),(⟨-27527936,-27527872⟩ : DyadicInterval 40),(⟨762123383246,762123402575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨213898864053,214153520352⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195450370624,195450370688⟩ : DyadicInterval 40),(⟨-237870095616,-237870095552⟩ : DyadicInterval 40),(⟨741184189522,741184208851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663533568,195663533632⟩ : DyadicInterval 40),(⟨-238186303616,-238186303552⟩ : DyadicInterval 40),(⟨741133978502,741133997831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42522770048,-42419724928⟩ : DyadicInterval 40),(⟨783333246080,783384787904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨195472760640,195663526464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238186292992,-237903302016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1052_ok : ecellOkT e1052 = true := by decide +kernel
theorem e1052_pos {a z : ℝ} (ha1 : ((159387/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((99723/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1052 e1052_ok ha1 ha2 hz1 hz2 hz

-- box ['99723/512000', '798633/4096000', '999/1000', '3997/4000']  interval_lower 389354995/1099511627776
noncomputable def e1053 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139605,0,true,195663526400,195663526464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115947,0,false,-238186292992,-238186292928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041308,0,true,195854259072,195854259136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214244,0,false,-238469356800,-238469356736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313450986093,0,true,195484269568,195484269632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885572269459,0,false,-237920371456,-237920371392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313732255249,0,true,195719699456,195719699520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885291000303,0,false,-238269646016,-238269645952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594207093,0,true,82576192,82576256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429048459,0,false,-82582464,-82582400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621858781,0,true,110225472,110225536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401396771,0,false,-110236544,-110236480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616724,0,false,-11072,-11008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621574,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313558058865,0,true,195573898304,195573898368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885465196687,0,false,-238053319232,-238053319168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313812657638,0,true,195786989120,195786989184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885210597914,0,false,-238369508480,-238369508416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057743145988,0,false,-42582519296,-42582519232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057842332514,0,false,-42479420928,-42479420864⟩
    { al := (99723/512000), au := (798633/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨214153511829,214381413532⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195484269568,195484269632⟩ : DyadicInterval 40),(⟨-237920371456,-237920371392⟩ : DyadicInterval 40),(⟨741176209294,741176228624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195719699456,195719699520⟩ : DyadicInterval 40),(⟨-238269646016,-238269645952⟩ : DyadicInterval 40),(⟨741120736679,741120756009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82579317,110231005⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82576192,82576256⟩ : DyadicInterval 40),(⟨-82582464,-82582400⟩ : DyadicInterval 40),(⟨762123380485,762123399815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110225472,110225536⟩ : DyadicInterval 40),(⟨-110236544,-110236480⟩ : DyadicInterval 40),(⟨762123378036,762123397366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11072,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123408416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214046431089,214301029862⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195573898304,195573898368⟩ : DyadicInterval 40),(⟨-238053319232,-238053319168⟩ : DyadicInterval 40),(⟨741155100943,741155120272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195786989120,195786989184⟩ : DyadicInterval 40),(⟨-238369508480,-238369508416⟩ : DyadicInterval 40),(⟨741104865778,741104885108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42582519296,-42479420864⟩ : DyadicInterval 40),(⟨783363094048,783414662528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195663526400,195854259136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238469356800,-238186292928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1053_ok : ecellOkT e1053 = true := by decide +kernel
theorem e1053_pos {a z : ℝ} (ha1 : ((99723/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((798633/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1053 e1053_ok ha1 ha2 hz1 hz2 hz

-- box ['798633/4096000', '399741/2048000', '999/1000', '3997/4000']  interval_lower 393645943/1099511627776
noncomputable def e1054 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041307,0,true,195854259072,195854259136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214245,0,false,-238469356800,-238469356736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943010,0,true,196044958656,196044958720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312542,0,false,-238752493504,-238752493440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313678659893,0,true,195674842560,195674842624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885344595659,0,false,-238203083776,-238203083712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313959986024,0,true,195910279296,195910279360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885063269528,0,false,-238552518912,-238552518848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594299987,0,true,82669056,82669120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428955565,0,false,-82675328,-82675264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099621982665,0,true,110349312,110349376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401272887,0,false,-110360448,-110360384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616699,0,false,-11136,-11072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621560,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313785846614,0,true,195764551168,195764551232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885237408938,0,false,-238336207296,-238336207232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314040473876,0,true,195977628864,195977628928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884982781676,0,false,-238652513280,-238652513216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057654293441,0,false,-42674884352,-42674884288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057753596575,0,false,-42571656128,-42571656064⟩
    { al := (798633/4096000), au := (399741/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨214381413531,214609315234⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195674842560,195674842624⟩ : DyadicInterval 40),(⟨-238203083776,-238203083712⟩ : DyadicInterval 40),(⟨741131312666,741131331996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195910279296,195910279360⟩ : DyadicInterval 40),(⟨-238552518912,-238552518848⟩ : DyadicInterval 40),(⟨741075768258,741075787588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82672211,110354889⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82669056,82669120⟩ : DyadicInterval 40),(⟨-82675328,-82675264⟩ : DyadicInterval 40),(⟨762123380471,762123399801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110349312,110349376⟩ : DyadicInterval 40),(⟨-110360448,-110360384⟩ : DyadicInterval 40),(⟨762123378043,762123397373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11136,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123408448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214274218838,214528846100⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195764551168,195764551232⟩ : DyadicInterval 40),(⟨-238336207296,-238336207232⟩ : DyadicInterval 40),(⟨741110158760,741110178089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195977628864,195977628928⟩ : DyadicInterval 40),(⟨-238652513280,-238652513216⟩ : DyadicInterval 40),(⟨741059863132,741059882462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42674884352,-42571656064⟩ : DyadicInterval 40),(⟨783409211648,783460845056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195854259072,196044958720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238752493504,-238469356736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1054_ok : ecellOkT e1054 = true := by decide +kernel
theorem e1054_pos {a z : ℝ} (ha1 : ((798633/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((399741/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1054 e1054_ok ha1 ha2 hz1 hz2 hz

-- box ['99723/512000', '798633/4096000', '3997/4000', '1999/2000']  interval_lower 388561579/1099511627776
noncomputable def e1055 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139605,0,true,195663526400,195663526464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115947,0,false,-238186292992,-238186292928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041308,0,true,195854259072,195854259136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214244,0,false,-238469356800,-238469356736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313504524471,0,true,195529086528,195529086592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885518731081,0,false,-237986845824,-237986845760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313785850602,0,true,195764554496,195764554560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885237404950,0,false,-238336212224,-238336212160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566680960,0,true,55051776,55051840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456574592,0,false,-55054592,-55054528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594301685,0,true,82670784,82670848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428953867,0,false,-82677056,-82676992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621559,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625020,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313584827406,0,true,195596304640,195596304704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885438428146,0,false,-238086559168,-238086559104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313839454852,0,true,195809415104,195809415168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885183800700,0,false,-238402793536,-238402793472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057732699478,0,false,-42593378368,-42593378304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057831909580,0,false,-42490254464,-42490254400⟩
    { al := (99723/512000), au := (798633/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨214153511829,214381413532⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195529086528,195529086592⟩ : DyadicInterval 40),(⟨-237986845824,-237986845760⟩ : DyadicInterval 40),(⟨741165656080,741165675410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195764554496,195764554560⟩ : DyadicInterval 40),(⟨-238336212224,-238336212160⟩ : DyadicInterval 40),(⟨741110157968,741110177298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55053184,82673909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55051776,55051840⟩ : DyadicInterval 40),(⟨-55054592,-55054528⟩ : DyadicInterval 40),(⟨762123382203,762123401532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82670784,82670848⟩ : DyadicInterval 40),(⟨-82677056,-82676992⟩ : DyadicInterval 40),(⟨762123380471,762123399800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214073199630,214327827076⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195596304640,195596304704⟩ : DyadicInterval 40),(⟨-238086559168,-238086559104⟩ : DyadicInterval 40),(⟨741149822111,741149841440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195809415104,195809415168⟩ : DyadicInterval 40),(⟨-238402793536,-238402793472⟩ : DyadicInterval 40),(⟨741099574822,741099594152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42593378368,-42490254400⟩ : DyadicInterval 40),(⟨783368510816,783420092064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195663526400,195854259136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238469356800,-238186292928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1055_ok : ecellOkT e1055 = true := by decide +kernel
theorem e1055_pos {a z : ℝ} (ha1 : ((99723/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((798633/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1055 e1055_ok ha1 ha2 hz1 hz2 hz

-- box ['798633/4096000', '399741/2048000', '3997/4000', '1999/2000']  interval_lower 196424751/549755813888
noncomputable def e1056 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041307,0,true,195854259072,195854259136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214245,0,false,-238469356800,-238469356736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943010,0,true,196044958656,196044958720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312542,0,false,-238752493504,-238752493440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313732255246,0,true,195719699456,195719699520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885291000306,0,false,-238269645952,-238269645888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314013638353,0,true,195955174272,195955174336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885009617199,0,false,-238619173056,-238619172992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566742891,0,true,55113728,55113792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456512661,0,false,-55116544,-55116480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594394600,0,true,82763648,82763712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428860952,0,false,-82769984,-82769920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621545,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625014,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313812643645,0,true,195786977408,195786977472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885210611907,0,false,-238369491136,-238369491072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314067299579,0,true,196000074816,196000074880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884955955973,0,false,-238685842304,-238685842240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057643824707,0,false,-42685767488,-42685767424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057743151444,0,false,-42582513664,-42582513600⟩
    { al := (798633/4096000), au := (399741/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨214381413531,214609315234⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195719699456,195719699520⟩ : DyadicInterval 40),(⟨-238269645952,-238269645888⟩ : DyadicInterval 40),(⟨741120736654,741120755983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195955174272,195955174336⟩ : DyadicInterval 40),(⟨-238619173056,-238619172992⟩ : DyadicInterval 40),(⟨741065166736,741065186066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55115115,82766824⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55113728,55113792⟩ : DyadicInterval 40),(⟨-55116544,-55116480⟩ : DyadicInterval 40),(⟨762123382197,762123401526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82763648,82763712⟩ : DyadicInterval 40),(⟨-82769984,-82769920⟩ : DyadicInterval 40),(⟨762123380489,762123399818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214301015869,214555671803⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195786977408,195786977472⟩ : DyadicInterval 40),(⟨-238369491136,-238369491072⟩ : DyadicInterval 40),(⟨741104868556,741104887886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196000074816,196000074880⟩ : DyadicInterval 40),(⟨-238685842304,-238685842240⟩ : DyadicInterval 40),(⟨741054560764,741054580093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42685767488,-42582513600⟩ : DyadicInterval 40),(⟨783414640416,783466286624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195854259072,196044958720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238752493504,-238469356736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1056_ok : ecellOkT e1056 = true := by decide +kernel
theorem e1056_pos {a z : ℝ} (ha1 : ((798633/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((399741/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1056 e1056_ok ha1 ha2 hz1 hz2 hz

-- box ['399741/2048000', '800331/4096000', '999/1000', '3997/4000']  interval_lower 49744315/137438953472
noncomputable def e1057 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943009,0,true,196044958656,196044958720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312543,0,false,-238752493504,-238752493440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844712,0,true,196235625152,196235625216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410840,0,false,-239035703104,-239035703040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313906333693,0,true,195865382528,195865382592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885116921859,0,false,-238485868800,-238485868736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314187716800,0,true,196100826176,196100826240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884835538752,0,false,-238835464640,-238835464576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594392899,0,true,82761984,82762048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428862653,0,false,-82768256,-82768192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622106571,0,true,110473216,110473280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401148981,0,false,-110484352,-110484288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616675,0,false,-11136,-11072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621546,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314013634364,0,true,195955170944,195955171008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885009621188,0,false,-238619168128,-238619168064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314268290120,0,true,196168235584,196168235648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884754965432,0,false,-238935590912,-238935590848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057565346485,0,false,-42767355328,-42767355264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057664766254,0,false,-42663997120,-42663997056⟩
    { al := (399741/2048000), au := (800331/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨214609315233,214837216936⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195865382528,195865382592⟩ : DyadicInterval 40),(⟨-238485868800,-238485868736⟩ : DyadicInterval 40),(⟨741086367031,741086386360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196100826176,196100826240⟩ : DyadicInterval 40),(⟨-238835464640,-238835464576⟩ : DyadicInterval 40),(⟨741030750779,741030770108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82765123,110478795⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82761984,82762048⟩ : DyadicInterval 40),(⟨-82768256,-82768192⟩ : DyadicInterval 40),(⟨762123380457,762123399787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110473216,110473280⟩ : DyadicInterval 40),(⟨-110484352,-110484288⟩ : DyadicInterval 40),(⟨762123378018,762123397348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11136,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123408448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214502006588,214756662344⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195955170944,195955171008⟩ : DyadicInterval 40),(⟨-238619168128,-238619168064⟩ : DyadicInterval 40),(⟨741065167530,741065186860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196168235584,196168235648⟩ : DyadicInterval 40),(⟨-238935590912,-238935590848⟩ : DyadicInterval 40),(⟨741014811388,741014830717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42767355328,-42663997056⟩ : DyadicInterval 40),(⟨783455382144,783507080544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196044958656,196235625216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239035703104,-238752493440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1057_ok : ecellOkT e1057 = true := by decide +kernel
theorem e1057_pos {a z : ℝ} (ha1 : ((399741/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((800331/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1057 e1057_ok ha1 ha2 hz1 hz2 hz

-- box ['800331/4096000', '40059/204800', '999/1000', '3997/4000']  interval_lower 100570373/274877906944
noncomputable def e1058 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844711,0,true,196235625152,196235625216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410841,0,false,-239035703104,-239035703040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746415,0,true,196426258560,196426258624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509137,0,false,-239318985728,-239318985664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314134007494,0,true,196055889536,196055889600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884889248058,0,false,-238768726528,-238768726464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314415447577,0,true,196291340032,196291340096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884607807975,0,false,-239118483136,-239118483072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594485826,0,true,82854912,82854976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428769726,0,false,-82861184,-82861120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622230500,0,true,110597120,110597184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099401025052,0,false,-110608320,-110608256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616650,0,false,-11136,-11072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621532,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314241422121,0,true,196145757696,196145757760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884781833431,0,false,-238902201792,-238902201728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314496106361,0,true,196358809216,196358809280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884527149191,0,false,-239218741504,-239218741440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057476305124,0,false,-42859932288,-42859932224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057575841547,0,false,-42756444096,-42756444032⟩
    { al := (800331/4096000), au := (40059/204800), zl := (999/1000), zu := (3997/4000),
      A := ⟨214837216935,215065118639⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196055889536,196055889600⟩ : DyadicInterval 40),(⟨-238768726528,-238768726464⟩ : DyadicInterval 40),(⟨741041372338,741041391667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196291340032,196291340096⟩ : DyadicInterval 40),(⟨-239118483136,-239118483072⟩ : DyadicInterval 40),(⟨740985684242,740985703571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82858050,110602724⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82854912,82854976⟩ : DyadicInterval 40),(⟨-82861184,-82861120⟩ : DyadicInterval 40),(⟨762123380443,762123399773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110597120,110597184⟩ : DyadicInterval 40),(⟨-110608320,-110608256⟩ : DyadicInterval 40),(⟨762123378025,762123397355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11136,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123408448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214729794345,214984478585⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196145757696,196145757760⟩ : DyadicInterval 40),(⟨-238902201792,-238902201728⟩ : DyadicInterval 40),(⟨741020127227,741020146556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196358809216,196358809280⟩ : DyadicInterval 40),(⟨-239218741504,-239218741440⟩ : DyadicInterval 40),(⟨740969710623,740969729953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42859932288,-42756444032⟩ : DyadicInterval 40),(⟨783501605632,783553369024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196235625152,196426258624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239318985728,-239035703040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1058_ok : ecellOkT e1058 = true := by decide +kernel
theorem e1058_pos {a z : ℝ} (ha1 : ((800331/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40059/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1058 e1058_ok ha1 ha2 hz1 hz2 hz

-- box ['399741/2048000', '800331/4096000', '3997/4000', '1999/2000']  interval_lower 397155285/1099511627776
noncomputable def e1059 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943009,0,true,196044958656,196044958720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312543,0,false,-238752493504,-238752493440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844712,0,true,196235625152,196235625216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410840,0,false,-239035703104,-239035703040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313959986022,0,true,195910279296,195910279360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885063269530,0,false,-238552518912,-238552518848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314241426104,0,true,196145761024,196145761088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884781829448,0,false,-238902206720,-238902206656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566804833,0,true,55175616,55175680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456450719,0,false,-55178496,-55178432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594487531,0,true,82856576,82856640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428768021,0,false,-82862912,-82862848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621531,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625008,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314040459876,0,true,195977617152,195977617216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884982795676,0,false,-238652495872,-238652495808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314295144309,0,true,196190701440,196190701504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884728111243,0,false,-238968963968,-238968963904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057554855506,0,false,-42778262464,-42778262400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057654298905,0,false,-42674878720,-42674878656⟩
    { al := (399741/2048000), au := (800331/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨214609315233,214837216936⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195910279296,195910279360⟩ : DyadicInterval 40),(⟨-238552518912,-238552518848⟩ : DyadicInterval 40),(⟨741075768259,741075787588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196145761024,196145761088⟩ : DyadicInterval 40),(⟨-238902206720,-238902206656⟩ : DyadicInterval 40),(⟨741020126432,741020145762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55177057,82859755⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55175616,55175680⟩ : DyadicInterval 40),(⟨-55178496,-55178432⟩ : DyadicInterval 40),(⟨762123382222,762123401552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82856576,82856640⟩ : DyadicInterval 40),(⟨-82862912,-82862848⟩ : DyadicInterval 40),(⟨762123380475,762123399804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214528832100,214783516533⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195977617152,195977617216⟩ : DyadicInterval 40),(⟨-238652495872,-238652495808⟩ : DyadicInterval 40),(⟨741059865892,741059885222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196190701440,196190701504⟩ : DyadicInterval 40),(⟨-238968963968,-238968963904⟩ : DyadicInterval 40),(⟨741009497644,741009516974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42778262464,-42674878656⟩ : DyadicInterval 40),(⟨783460822944,783512534112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196044958656,196235625216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239035703104,-238752493440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1059_ok : ecellOkT e1059 = true := by decide +kernel
theorem e1059_pos {a z : ℝ} (ha1 : ((399741/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((800331/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1059 e1059_ok ha1 ha2 hz1 hz2 hz

-- box ['800331/4096000', '40059/204800', '3997/4000', '1999/2000']  interval_lower 200739411/549755813888
noncomputable def e1060 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844711,0,true,196235625152,196235625216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410841,0,false,-239035703104,-239035703040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746415,0,true,196426258560,196426258624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509137,0,false,-239318985728,-239318985664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314187716798,0,true,196100826176,196100826240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884835538754,0,false,-238835464640,-238835464576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314469213856,0,true,196336314688,196336314752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884554041696,0,false,-239185313280,-239185313216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566866787,0,true,55237568,55237632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456388765,0,false,-55240448,-55240384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594580479,0,true,82949568,82949632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428675073,0,false,-82955840,-82955776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621517,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625001,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314268276114,0,true,196168223872,196168223936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884754979438,0,false,-238935573568,-238935573504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314522989028,0,true,196381294976,196381295040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884500266524,0,false,-239252158528,-239252158464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057465791879,0,false,-42870863488,-42870863424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057565351957,0,false,-42767349696,-42767349632⟩
    { al := (800331/4096000), au := (40059/204800), zl := (3997/4000), zu := (1999/2000),
      A := ⟨214837216935,215065118639⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196100826176,196100826240⟩ : DyadicInterval 40),(⟨-238835464640,-238835464576⟩ : DyadicInterval 40),(⟨741030750779,741030770109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196336314688,196336314752⟩ : DyadicInterval 40),(⟨-239185313280,-239185313216⟩ : DyadicInterval 40),(⟨740975037109,740975056439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55239011,82952703⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55237568,55237632⟩ : DyadicInterval 40),(⟨-55240448,-55240384⟩ : DyadicInterval 40),(⟨762123382216,762123401545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82949568,82949632⟩ : DyadicInterval 40),(⟨-82955840,-82955776⟩ : DyadicInterval 40),(⟨762123380429,762123399758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214756648338,215011361252⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196168223872,196168223936⟩ : DyadicInterval 40),(⟨-238935573568,-238935573504⟩ : DyadicInterval 40),(⟨741014814181,741014833510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196381294976,196381295040⟩ : DyadicInterval 40),(⟨-239252158528,-239252158464⟩ : DyadicInterval 40),(⟨740964385455,740964404785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42870863488,-42767349632⟩ : DyadicInterval 40),(⟨783507058432,783558834624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196235625152,196426258624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239318985728,-239035703040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1060_ok : ecellOkT e1060 = true := by decide +kernel
theorem e1060_pos {a z : ℝ} (ha1 : ((800331/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40059/204800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1060 e1060_ok ha1 ha2 hz1 hz2 hz

-- box ['99723/512000', '798633/4096000', '1999/2000', '3999/4000']  interval_lower 387767411/1099511627776
noncomputable def e1061 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139605,0,true,195663526400,195663526464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115947,0,false,-238186292992,-238186292928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041308,0,true,195854259072,195854259136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214244,0,false,-238469356800,-238469356736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313558062849,0,true,195573901632,195573901696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885465192703,0,false,-238053324224,-238053324160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1313839445955,0,true,195809407680,195809407744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨885183809597,0,false,-238402782528,-238402782464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539154435,0,true,27526272,27526336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484101117,0,false,-27527040,-27526976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566744195,0,true,55115008,55115072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456511357,0,false,-55117824,-55117760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625013,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627087,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313611596128,0,true,195618710656,195618710720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885411659424,0,false,-238119800256,-238119800192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1313866252246,0,true,195831840832,195831840896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨885157003306,0,false,-238436079872,-238436079808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057722251592,0,false,-42604239040,-42604238976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057821485271,0,false,-42501089536,-42501089472⟩
    { al := (99723/512000), au := (798633/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨214153511829,214381413532⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195573901632,195573901696⟩ : DyadicInterval 40),(⟨-238053324224,-238053324160⟩ : DyadicInterval 40),(⟨741155100179,741155119509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195809407680,195809407744⟩ : DyadicInterval 40),(⟨-238402782528,-238402782464⟩ : DyadicInterval 40),(⟨741099576584,741099595913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27526659,55116419⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27526272,27526336⟩ : DyadicInterval 40),(⟨-27527040,-27526976⟩ : DyadicInterval 40),(⟨762123383246,762123402575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55115008,55115072⟩ : DyadicInterval 40),(⟨-55117824,-55117760⟩ : DyadicInterval 40),(⟨762123382197,762123401526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214099968352,214354624470⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195618710656,195618710720⟩ : DyadicInterval 40),(⟨-238119800256,-238119800192⟩ : DyadicInterval 40),(⟨741144542543,741144561873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195831840832,195831840896⟩ : DyadicInterval 40),(⟨-238436079872,-238436079808⟩ : DyadicInterval 40),(⟨741094283141,741094302471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42604239040,-42501089472⟩ : DyadicInterval 40),(⟨783373928352,783425522400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195663526400,195854259136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238469356800,-238186292928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1061_ok : ecellOkT e1061 = true := by decide +kernel
theorem e1061_pos {a z : ℝ} (ha1 : ((99723/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((798633/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1061 e1061_ok ha1 ha2 hz1 hz2 hz

-- box ['798633/4096000', '399741/2048000', '1999/2000', '3999/4000']  interval_lower 196026085/549755813888
noncomputable def e1062 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041307,0,true,195854259072,195854259136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214245,0,false,-238469356800,-238469356736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943010,0,true,196044958656,196044958720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312542,0,false,-238752493504,-238752493440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313785850600,0,true,195764554496,195764554560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885237404952,0,false,-238336212224,-238336212160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314067290682,0,true,196000067392,196000067456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884955964870,0,false,-238685831232,-238685831168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539185402,0,true,27557248,27557312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484070150,0,false,-27558016,-27557952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566806138,0,true,55176960,55177024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456449414,0,false,-55179776,-55179712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625006,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627086,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1313839440855,0,true,195809403392,195809403456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨885183814697,0,false,-238402776192,-238402776128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314094125466,0,true,196022520448,196022520512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884929130086,0,false,-238719172608,-238719172544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057633354593,0,false,-42696652096,-42696652032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057732704936,0,false,-42593372736,-42593372672⟩
    { al := (798633/4096000), au := (399741/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨214381413531,214609315234⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195764554496,195764554560⟩ : DyadicInterval 40),(⟨-238336212224,-238336212160⟩ : DyadicInterval 40),(⟨741110157969,741110177298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196000067392,196000067456⟩ : DyadicInterval 40),(⟨-238685831232,-238685831168⟩ : DyadicInterval 40),(⟨741054562503,741054581832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27557626,55178362⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27557248,27557312⟩ : DyadicInterval 40),(⟨-27558016,-27557952⟩ : DyadicInterval 40),(⟨762123383245,762123402574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55176960,55177024⟩ : DyadicInterval 40),(⟨-55179776,-55179712⟩ : DyadicInterval 40),(⟨762123382190,762123401519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214327813079,214582497690⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195809403392,195809403456⟩ : DyadicInterval 40),(⟨-238402776192,-238402776128⟩ : DyadicInterval 40),(⟨741099577602,741099596931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196022520448,196022520512⟩ : DyadicInterval 40),(⟨-238719172608,-238719172544⟩ : DyadicInterval 40),(⟨741049257704,741049277033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42696652096,-42593372672⟩ : DyadicInterval 40),(⟨783420069952,783471728928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨195854259072,196044958720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238752493504,-238469356736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1062_ok : ecellOkT e1062 = true := by decide +kernel
theorem e1062_pos {a z : ℝ} (ha1 : ((798633/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((399741/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1062 e1062_ok ha1 ha2 hz1 hz2 hz

-- box ['99723/512000', '798633/4096000', '3999/4000', '1']  interval_lower 386973083/1099511627776
noncomputable def e1063 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313665139605,0,true,195663526400,195663526464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885358115947,0,false,-238186292992,-238186292928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041308,0,true,195854259072,195854259136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214244,0,false,-238469356800,-238469356736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313611601227,0,true,195618714944,195618715008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885411654325,0,false,-238119806592,-238119806528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539186310,0,true,27558144,27558208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484069242,0,false,-27558912,-27558848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627085,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1313638365042,0,true,195641116416,195641116480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨885384890510,0,false,-238153042624,-238153042560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893049832,0,true,195854266176,195854266240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨885130205720,0,false,-238469367424,-238469367360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057711802324,0,false,-42615101184,-42615101120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057811059584,0,false,-42511926208,-42511926144⟩
    { al := (99723/512000), au := (798633/4096000), zl := (3999/4000), zu := 1,
      A := ⟨214153511829,214381413532⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195663526400,195663526464⟩ : DyadicInterval 40),(⟨-238186292992,-238186292928⟩ : DyadicInterval 40),(⟨741133980188,741133999518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195618714944,195618715008⟩ : DyadicInterval 40),(⟨-238119806592,-238119806528⟩ : DyadicInterval 40),(⟨741144541527,741144560857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27558534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27558144,27558208⟩ : DyadicInterval 40),(⟨-27558912,-27558848⟩ : DyadicInterval 40),(⟨762123383245,762123402574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨214126737266,214381422056⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195641116416,195641116480⟩ : DyadicInterval 40),(⟨-238153042624,-238153042560⟩ : DyadicInterval 40),(⟨741139262251,741139281581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854266176,195854266240⟩ : DyadicInterval 40),(⟨-238469367424,-238469367360⟩ : DyadicInterval 40),(⟨741088990784,741089010113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42615101184,-42511926144⟩ : DyadicInterval 40),(⟨783379346688,783430953472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨195663526400,195854259136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238469356800,-238186292928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1063_ok : ecellOkT e1063 = true := by decide +kernel
theorem e1063_pos {a z : ℝ} (ha1 : ((99723/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((798633/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1063 e1063_ok ha1 ha2 hz1 hz2 hz

-- box ['798633/4096000', '399741/2048000', '3999/4000', '1']  interval_lower 391254715/1099511627776
noncomputable def e1064 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1313893041307,0,true,195854259072,195854259136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨885130214245,0,false,-238469356800,-238469356736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943010,0,true,196044958656,196044958720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312542,0,false,-238752493504,-238752493440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1313839445953,0,true,195809407680,195809407744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885183809599,0,false,-238402782528,-238402782464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539217284,0,true,27589120,27589184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484038268,0,false,-27589888,-27589824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627083,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1313866238249,0,true,195831829120,195831829184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨885157017303,0,false,-238436062464,-238436062400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120951535,0,true,196044965760,196044965824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨884902304017,0,false,-238752504064,-238752504000⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057622883099,0,false,-42707538304,-42707538240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057722257050,0,false,-42604233344,-42604233280⟩
    { al := (798633/4096000), au := (399741/2048000), zl := (3999/4000), zu := 1,
      A := ⟨214381413531,214609315234⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195854259072,195854259136⟩ : DyadicInterval 40),(⟨-238469356800,-238469356736⟩ : DyadicInterval 40),(⟨741088992435,741089011765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195809407680,195809407744⟩ : DyadicInterval 40),(⟨-238402782528,-238402782464⟩ : DyadicInterval 40),(⟨741099576584,741099595914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27589508⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27589120,27589184⟩ : DyadicInterval 40),(⟨-27589888,-27589824⟩ : DyadicInterval 40),(⟨762123383243,762123402572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨214354610473,214609323759⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195831829120,195831829184⟩ : DyadicInterval 40),(⟨-238436062464,-238436062400⟩ : DyadicInterval 40),(⟨741094285896,741094305226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044965760,196044965824⟩ : DyadicInterval 40),(⟨-238752504064,-238752504000⟩ : DyadicInterval 40),(⟨741043953902,741043973231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42707538304,-42604233280⟩ : DyadicInterval 40),(⟨783425500256,783477172032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨195854259072,196044958720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-238752493504,-238469356736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1064_ok : ecellOkT e1064 = true := by decide +kernel
theorem e1064_pos {a z : ℝ} (ha1 : ((798633/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((399741/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1064 e1064_ok ha1 ha2 hz1 hz2 hz

-- box ['399741/2048000', '800331/4096000', '1999/2000', '3999/4000']  interval_lower 49544361/137438953472
noncomputable def e1065 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943009,0,true,196044958656,196044958720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312543,0,false,-238752493504,-238752493440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844712,0,true,196235625152,196235625216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410840,0,false,-239035703104,-239035703040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314013638351,0,true,195955174272,195955174336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨885009617201,0,false,-238619173056,-238619172992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314295135408,0,true,196190694016,196190694080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884728120144,0,false,-238968952896,-238968952832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539216374,0,true,27588224,27588288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484039178,0,false,-27588992,-27588928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566868095,0,true,55238912,55238976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456387457,0,false,-55241728,-55241664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625000,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627084,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314067285578,0,true,196000063104,196000063168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884955969974,0,false,-238685824896,-238685824832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314321998680,0,true,196213166976,196213167040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884701256872,0,false,-239002338240,-239002338176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057544363144,0,false,-42789171200,-42789171136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057643830173,0,false,-42685761792,-42685761728⟩
    { al := (399741/2048000), au := (800331/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨214609315233,214837216936⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨195955174272,195955174336⟩ : DyadicInterval 40),(⟨-238619173056,-238619172992⟩ : DyadicInterval 40),(⟨741065166736,741065186066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196190694016,196190694080⟩ : DyadicInterval 40),(⟨-238968952896,-238968952832⟩ : DyadicInterval 40),(⟨741009499388,741009518718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27588598,55240319⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27588224,27588288⟩ : DyadicInterval 40),(⟨-27588992,-27588928⟩ : DyadicInterval 40),(⟨762123383243,762123402572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55238912,55238976⟩ : DyadicInterval 40),(⟨-55241728,-55241664⟩ : DyadicInterval 40),(⟨762123382184,762123401513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214555657802,214810370904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196000063104,196000063168⟩ : DyadicInterval 40),(⟨-238685824896,-238685824832⟩ : DyadicInterval 40),(⟨741054563524,741054582854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196213166976,196213167040⟩ : DyadicInterval 40),(⟨-239002338240,-239002338176⟩ : DyadicInterval 40),(⟨741004183182,741004202511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42789171200,-42685761728⟩ : DyadicInterval 40),(⟨783466264480,783517988480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196044958656,196235625216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239035703104,-238752493440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1065_ok : ecellOkT e1065 = true := by decide +kernel
theorem e1065_pos {a z : ℝ} (ha1 : ((399741/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((800331/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1065 e1065_ok ha1 ha2 hz1 hz2 hz

-- box ['800331/4096000', '40059/204800', '1999/2000', '3999/4000']  interval_lower 400675509/1099511627776
noncomputable def e1066 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844711,0,true,196235625152,196235625216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410841,0,false,-239035703104,-239035703040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746415,0,true,196426258560,196426258624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509137,0,false,-239318985728,-239318985664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314241426102,0,true,196145761024,196145761088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884781829450,0,false,-238902206720,-238902206656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314522980136,0,true,196381287552,196381287616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884500275416,0,false,-239252147456,-239252147392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539247351,0,true,27619200,27619264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484008201,0,false,-27619968,-27619904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566930061,0,true,55300864,55300928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456325491,0,false,-55303680,-55303616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624994,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627083,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314295130302,0,true,196190689728,196190689792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884728125250,0,false,-238968946560,-238968946496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314549871887,0,true,196403780544,196403780608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884473383665,0,false,-239285576768,-239285576704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057455277245,0,false,-42881796224,-42881796160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057554860979,0,false,-42778256832,-42778256768⟩
    { al := (800331/4096000), au := (40059/204800), zl := (1999/2000), zu := (3999/4000),
      A := ⟨214837216935,215065118639⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196145761024,196145761088⟩ : DyadicInterval 40),(⟨-238902206720,-238902206656⟩ : DyadicInterval 40),(⟨741020126433,741020145762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196381287552,196381287616⟩ : DyadicInterval 40),(⟨-239252147456,-239252147392⟩ : DyadicInterval 40),(⟨740964387202,740964406531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27619575,55302285⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27619200,27619264⟩ : DyadicInterval 40),(⟨-27619968,-27619904⟩ : DyadicInterval 40),(⟨762123383242,762123402571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55300864,55300928⟩ : DyadicInterval 40),(⟨-55303680,-55303616⟩ : DyadicInterval 40),(⟨762123382178,762123401507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214783502526,215038244111⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196190689728,196190689792⟩ : DyadicInterval 40),(⟨-238968946560,-238968946496⟩ : DyadicInterval 40),(⟨741009500413,741009519742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196403780544,196403780608⟩ : DyadicInterval 40),(⟨-239285576768,-239285576704⟩ : DyadicInterval 40),(⟨740959059487,740959078816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42881796224,-42778256768⟩ : DyadicInterval 40),(⟨783512512000,783564300992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196235625152,196426258624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239318985728,-239035703040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1066_ok : ecellOkT e1066 = true := by decide +kernel
theorem e1066_pos {a z : ℝ} (ha1 : ((800331/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40059/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1066 e1066_ok ha1 ha2 hz1 hz2 hz

-- box ['399741/2048000', '800331/4096000', '3999/4000', '1']  interval_lower 197777071/549755813888
noncomputable def e1067 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314120943009,0,true,196044958656,196044958720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884902312543,0,false,-238752493504,-238752493440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844712,0,true,196235625152,196235625216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410840,0,false,-239035703104,-239035703040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314067290680,0,true,196000067392,196000067456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884955964872,0,false,-238685831232,-238685831168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539248263,0,true,27620096,27620160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484007289,0,false,-27620864,-27620800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627082,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1314094111464,0,true,196022508736,196022508800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨884929144088,0,false,-238719155200,-238719155136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348853237,0,true,196235632256,196235632320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨884674402315,0,false,-239035713728,-239035713664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057533869398,0,false,-42800081408,-42800081344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057633360060,0,false,-42696646400,-42696646336⟩
    { al := (399741/2048000), au := (800331/4096000), zl := (3999/4000), zu := 1,
      A := ⟨214609315233,214837216936⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196044958656,196044958720⟩ : DyadicInterval 40),(⟨-238752493504,-238752493440⟩ : DyadicInterval 40),(⟨741043955584,741043974913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196000067392,196000067456⟩ : DyadicInterval 40),(⟨-238685831232,-238685831168⟩ : DyadicInterval 40),(⟨741054562503,741054581833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27620487⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27620096,27620160⟩ : DyadicInterval 40),(⟨-27620864,-27620800⟩ : DyadicInterval 40),(⟨762123383242,762123402571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨214582483688,214837225461⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196022508736,196022508800⟩ : DyadicInterval 40),(⟨-238719155200,-238719155136⟩ : DyadicInterval 40),(⟨741049260466,741049279795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235632256,196235632320⟩ : DyadicInterval 40),(⟨-239035713728,-239035713664⟩ : DyadicInterval 40),(⟨740998867961,740998887290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42800081408,-42696646336⟩ : DyadicInterval 40),(⟨783471706784,783523443584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨196044958656,196235625216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239035703104,-238752493440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1067_ok : ecellOkT e1067 = true := by decide +kernel
theorem e1067_pos {a z : ℝ} (ha1 : ((399741/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((800331/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1067 e1067_ok ha1 ha2 hz1 hz2 hz

-- box ['800331/4096000', '40059/204800', '3999/4000', '1']  interval_lower 99967901/274877906944
noncomputable def e1068 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314348844711,0,true,196235625152,196235625216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884674410841,0,false,-239035703104,-239035703040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746415,0,true,196426258560,196426258624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509137,0,false,-239318985728,-239318985664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314295135406,0,true,196190694016,196190694080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884728120146,0,false,-238968952896,-238968952832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539279246,0,true,27651072,27651136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483976306,0,false,-27651840,-27651776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627080,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1314321984673,0,true,196213155264,196213155328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨884701270879,0,false,-239002320832,-239002320768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576754930,0,true,196426265728,196426265792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨884446500622,0,false,-239318996288,-239318996224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057444761224,0,false,-42892730560,-42892730496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057544368618,0,false,-42789165504,-42789165440⟩
    { al := (800331/4096000), au := (40059/204800), zl := (3999/4000), zu := 1,
      A := ⟨214837216935,215065118639⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196235625152,196235625216⟩ : DyadicInterval 40),(⟨-239035703104,-239035703040⟩ : DyadicInterval 40),(⟨740998869620,740998888950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196190694016,196190694080⟩ : DyadicInterval 40),(⟨-238968952896,-238968952832⟩ : DyadicInterval 40),(⟨741009499389,741009518718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27651470⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27651072,27651136⟩ : DyadicInterval 40),(⟨-27651840,-27651776⟩ : DyadicInterval 40),(⟨762123383240,762123402569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨214810356897,215065127154⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196213155264,196213155328⟩ : DyadicInterval 40),(⟨-239002320832,-239002320768⟩ : DyadicInterval 40),(⟨741004185951,741004205280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426265728,196426265792⟩ : DyadicInterval 40),(⟨-239318996288,-239318996224⟩ : DyadicInterval 40),(⟨740953732859,740953752188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42892730560,-42789165440⟩ : DyadicInterval 40),(⟨783517966336,783569768160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨196235625152,196426258624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239318985728,-239035703040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1068_ok : ecellOkT e1068 = true := by decide +kernel
theorem e1068_pos {a z : ℝ} (ha1 : ((800331/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((40059/204800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1068 e1068_ok ha1 ha2 hz1 hz2 hz

-- box ['40059/204800', '802029/4096000', '999/1000', '3997/4000']  interval_lower 406625851/1099511627776
noncomputable def e1069 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746414,0,true,196426258560,196426258624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509138,0,false,-239318985728,-239318985664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648117,0,true,196616859008,196616859072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607435,0,false,-239602341312,-239602341248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314361681295,0,true,196246363456,196246363520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884661574257,0,false,-239051657088,-239051657024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314643178352,0,true,196481820864,196481820928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884380077200,0,false,-239401574592,-239401574528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594578771,0,true,82947840,82947904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428676781,0,false,-82954176,-82954112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622354451,0,true,110721088,110721152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400901101,0,false,-110732288,-110732224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616625,0,false,-11200,-11136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621518,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314469209863,0,true,196336311360,196336311424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884554045689,0,false,-239185308288,-239185308224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314723922605,0,true,196549349824,196549349888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884299332947,0,false,-239501964992,-239501964928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057387169356,0,false,-42952615168,-42952615104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057486822463,0,false,-42848996928,-42848996864⟩
    { al := (40059/204800), au := (802029/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨215065118638,215293020341⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550360,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196246363456,196246363520⟩ : DyadicInterval 40),(⟨-239051657088,-239051657024⟩ : DyadicInterval 40),(⟨740996328704,740996348033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196481820864,196481820928⟩ : DyadicInterval 40),(⟨-239401574592,-239401574528⟩ : DyadicInterval 40),(⟨740940568712,740940588042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82950995,110726675⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82947840,82947904⟩ : DyadicInterval 40),(⟨-82954176,-82954112⟩ : DyadicInterval 40),(⟨762123380461,762123399791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110721088,110721152⟩ : DyadicInterval 40),(⟨-110732288,-110732224⟩ : DyadicInterval 40),(⟨762123378000,762123397330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11200,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123408480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214957582087,215212294829⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196336311360,196336311424⟩ : DyadicInterval 40),(⟨-239185308288,-239185308224⟩ : DyadicInterval 40),(⟨740975037881,740975057210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196549349824,196549349888⟩ : DyadicInterval 40),(⟨-239501964992,-239501964928⟩ : DyadicInterval 40),(⟨740924560762,740924580091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42952615168,-42848996864⟩ : DyadicInterval 40),(⟨783547882048,783599710464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196426258560,196616859072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239602341312,-239318985664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1069_ok : ecellOkT e1069 = true := by decide +kernel
theorem e1069_pos {a z : ℝ} (ha1 : ((40059/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((802029/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1069 e1069_ok ha1 ha2 hz1 hz2 hz

-- box ['802029/4096000', '401439/2048000', '999/1000', '3997/4000']  interval_lower 410988581/1099511627776
noncomputable def e1070 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648116,0,true,196616859008,196616859072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607436,0,false,-239602341312,-239602341248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549819,0,true,196807426368,196807426432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705733,0,false,-239885769920,-239885769856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314589355095,0,true,196436804416,196436804480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884433900457,0,false,-239334660480,-239334660416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314870909128,0,true,196672268672,196672268736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884152346424,0,false,-239684738880,-239684738816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594671732,0,true,83040768,83040832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428583820,0,false,-83047104,-83047040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622478425,0,true,110845056,110845120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400777127,0,false,-110856256,-110856192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616600,0,false,-11200,-11136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621504,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314696997617,0,true,196526832064,196526832128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884326257935,0,false,-239468487744,-239468487680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314951738847,0,true,196739857408,196739857472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884071516705,0,false,-239785261440,-239785261376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057297939183,0,false,-43045404032,-43045403968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057397708993,0,false,-42941655680,-42941655616⟩
    { al := (802029/4096000), au := (401439/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨215293020340,215520922043⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550361,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196436804416,196436804480⟩ : DyadicInterval 40),(⟨-239334660480,-239334660416⟩ : DyadicInterval 40),(⟨740951236038,740951255367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196672268672,196672268736⟩ : DyadicInterval 40),(⟨-239684738880,-239684738816⟩ : DyadicInterval 40),(⟨740895404125,740895423455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83043956,110850649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83040768,83040832⟩ : DyadicInterval 40),(⟨-83047104,-83047040⟩ : DyadicInterval 40),(⟨762123380447,762123399777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110845056,110845120⟩ : DyadicInterval 40),(⟨-110856256,-110856192⟩ : DyadicInterval 40),(⟨762123377975,762123397305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11200,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123408480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215185369841,215440111071⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196526832064,196526832128⟩ : DyadicInterval 40),(⟨-239468487744,-239468487680⟩ : DyadicInterval 40),(⟨740929899449,740929918779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196739857408,196739857472⟩ : DyadicInterval 40),(⟨-239785261440,-239785261376⟩ : DyadicInterval 40),(⟨740879361817,740879381147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43045404032,-42941655616⟩ : DyadicInterval 40),(⟨783594211424,783646104896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196616859008,196807426432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239885769920,-239602341248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1070_ok : ecellOkT e1070 = true := by decide +kernel
theorem e1070_pos {a z : ℝ} (ha1 : ((802029/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((401439/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1070 e1070_ok ha1 ha2 hz1 hz2 hz

-- box ['40059/204800', '802029/4096000', '3997/4000', '1999/2000']  interval_lower 202910161/549755813888
noncomputable def e1071 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746414,0,true,196426258560,196426258624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509138,0,false,-239318985728,-239318985664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648117,0,true,196616859008,196616859072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607435,0,false,-239602341312,-239602341248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314415447574,0,true,196291340032,196291340096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884607807978,0,false,-239118483136,-239118483072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314697001608,0,true,196526835392,196526835456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884326253944,0,false,-239468492736,-239468492672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566928751,0,true,55299584,55299648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456326801,0,false,-55302400,-55302336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594673445,0,true,83042496,83042560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428582107,0,false,-83048832,-83048768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621503,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624995,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314496092350,0,true,196358797504,196358797568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884527163202,0,false,-239218724096,-239218724032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314750833762,0,true,196571855552,196571855616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884272421790,0,false,-239535426048,-239535425984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057376633817,0,false,-42963570432,-42963570368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057476310604,0,false,-42859926592,-42859926528⟩
    { al := (40059/204800), au := (802029/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨215065118638,215293020341⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550360,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196291340032,196291340096⟩ : DyadicInterval 40),(⟨-239118483136,-239118483072⟩ : DyadicInterval 40),(⟨740985684242,740985703572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196526835392,196526835456⟩ : DyadicInterval 40),(⟨-239468492736,-239468492672⟩ : DyadicInterval 40),(⟨740929898676,740929918006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55300975,83045669⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55299584,55299648⟩ : DyadicInterval 40),(⟨-55302400,-55302336⟩ : DyadicInterval 40),(⟨762123382178,762123401507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83042496,83042560⟩ : DyadicInterval 40),(⟨-83048832,-83048768⟩ : DyadicInterval 40),(⟨762123380447,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨214984464574,215239205986⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196358797504,196358797568⟩ : DyadicInterval 40),(⟨-239218724096,-239218724032⟩ : DyadicInterval 40),(⟨740969713398,740969732727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196571855552,196571855616⟩ : DyadicInterval 40),(⟨-239535426048,-239535425984⟩ : DyadicInterval 40),(⟨740919224128,740919243458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42963570432,-42859926528⟩ : DyadicInterval 40),(⟨783553346880,783605188096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196426258560,196616859072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239602341312,-239318985664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1071_ok : ecellOkT e1071 = true := by decide +kernel
theorem e1071_pos {a z : ℝ} (ha1 : ((40059/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((802029/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1071 e1071_ok ha1 ha2 hz1 hz2 hz

-- box ['802029/4096000', '401439/2048000', '3997/4000', '1999/2000']  interval_lower 102544939/274877906944
noncomputable def e1072 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648116,0,true,196616859008,196616859072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607436,0,false,-239602341312,-239602341248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549819,0,true,196807426368,196807426432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705733,0,false,-239885769920,-239885769856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314643178350,0,true,196481820864,196481820928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884380077202,0,false,-239401574592,-239401574528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314924789359,0,true,196717323072,196717323136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884098466193,0,false,-239751745152,-239751745088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566990726,0,true,55361536,55361600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456264826,0,false,-55364352,-55364288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594766426,0,true,83135488,83135552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428489126,0,false,-83141824,-83141760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621489,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624989,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314723908589,0,true,196549338112,196549338176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884299346963,0,false,-239501947584,-239501947520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314978678490,0,true,196762383104,196762383168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884044577062,0,false,-239818766592,-239818766528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057287381328,0,false,-43056383424,-43056383360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057387174844,0,false,-42952609408,-42952609344⟩
    { al := (802029/4096000), au := (401439/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨215293020340,215520922043⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550361,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196481820864,196481820928⟩ : DyadicInterval 40),(⟨-239401574592,-239401574528⟩ : DyadicInterval 40),(⟨740940568713,740940588042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196717323072,196717323136⟩ : DyadicInterval 40),(⟨-239751745152,-239751745088⟩ : DyadicInterval 40),(⟨740884711186,740884730516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55362950,83138650⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55361536,55361600⟩ : DyadicInterval 40),(⟨-55364352,-55364288⟩ : DyadicInterval 40),(⟨762123382172,762123401501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83135488,83135552⟩ : DyadicInterval 40),(⟨-83141824,-83141760⟩ : DyadicInterval 40),(⟨762123380433,762123399762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215212280813,215467050714⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196549338112,196549338176⟩ : DyadicInterval 40),(⟨-239501947584,-239501947520⟩ : DyadicInterval 40),(⟨740924563543,740924582872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196762383104,196762383168⟩ : DyadicInterval 40),(⟨-239818766592,-239818766528⟩ : DyadicInterval 40),(⟨740874013719,740874033049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43056383424,-42952609344⟩ : DyadicInterval 40),(⟨783599688288,783651594592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196616859008,196807426432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239885769920,-239602341248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1072_ok : ecellOkT e1072 = true := by decide +kernel
theorem e1072_pos {a z : ℝ} (ha1 : ((802029/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((401439/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1072 e1072_ok ha1 ha2 hz1 hz2 hz

-- box ['401439/2048000', '803727/4096000', '999/1000', '3997/4000']  interval_lower 415369341/1099511627776
noncomputable def e1073 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549818,0,true,196807426368,196807426432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705734,0,false,-239885769920,-239885769856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451521,0,true,196997960704,196997960768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804031,0,false,-240169271616,-240169271552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314817028895,0,true,196627212416,196627212480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884206226657,0,false,-239617736704,-239617736640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315098639904,0,true,196862683520,196862683584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883924615648,0,false,-239967976128,-239967976064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594764710,0,true,83133760,83133824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428490842,0,false,-83140096,-83140032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622602420,0,true,110969024,110969088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400653132,0,false,-110980288,-110980224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616575,0,false,-11264,-11200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621490,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314924785370,0,true,196717319744,196717319808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884098470182,0,false,-239751740160,-239751740096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315179555090,0,true,196930332032,196930332096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883843700462,0,false,-240068630976,-240068630912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057208614604,0,false,-43138298880,-43138298816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057308501141,0,false,-43034420416,-43034420352⟩
    { al := (401439/2048000), au := (803727/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨215520922042,215748823745⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196627212416,196627212480⟩ : DyadicInterval 40),(⟨-239617736704,-239617736640⟩ : DyadicInterval 40),(⟨740906094330,740906113659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196862683520,196862683584⟩ : DyadicInterval 40),(⟨-239967976128,-239967976064⟩ : DyadicInterval 40),(⟨740850190482,740850209812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83136934,110974644⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83133760,83133824⟩ : DyadicInterval 40),(⟨-83140096,-83140032⟩ : DyadicInterval 40),(⟨762123380433,762123399763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨110969024,110969088⟩ : DyadicInterval 40),(⟨-110980288,-110980224⟩ : DyadicInterval 40),(⟨762123377982,762123397312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11264,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123408512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215413157594,215667927314⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196717319744,196717319808⟩ : DyadicInterval 40),(⟨-239751740160,-239751740096⟩ : DyadicInterval 40),(⟨740884711961,740884731290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196930332032,196930332096⟩ : DyadicInterval 40),(⟨-240068630976,-240068630912⟩ : DyadicInterval 40),(⟨740834113790,740834133119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43138298880,-43034420352⟩ : DyadicInterval 40),(⟨783640593792,783692552320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196807426368,196997960768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240169271616,-239885769856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1073_ok : ecellOkT e1073 = true := by decide +kernel
theorem e1073_pos {a z : ℝ} (ha1 : ((401439/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((803727/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1073 e1073_ok ha1 ha2 hz1 hz2 hz

-- box ['803727/4096000', '25143/128000', '999/1000', '3997/4000']  interval_lower 419768409/1099511627776
noncomputable def e1074 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451520,0,true,196997960704,196997960768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804032,0,false,-240169271616,-240169271552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353223,0,true,197188462016,197188462080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902329,0,false,-240452846464,-240452846400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315044702696,0,true,196817587456,196817587520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883978552856,0,false,-239900885824,-239900885760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315326370680,0,true,197053065408,197053065472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883696884872,0,false,-240251286400,-240251286336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594857705,0,true,83226752,83226816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428397847,0,false,-83233088,-83233024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622726438,0,true,111092992,111093056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400529114,0,false,-111104320,-111104256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616550,0,false,-11264,-11200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621476,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315152573124,0,true,196907774464,196907774528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883870682428,0,false,-240035065600,-240035065536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315407371328,0,true,197120773632,197120773696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883615884224,0,false,-240352073472,-240352073408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057119195621,0,false,-43231299776,-43231299712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057219198905,0,false,-43127291136,-43127291072⟩
    { al := (803727/4096000), au := (25143/128000), zl := (999/1000), zu := (3997/4000),
      A := ⟨215748823744,215976725447⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703044,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196817587456,196817587520⟩ : DyadicInterval 40),(⟨-239900885824,-239900885760⟩ : DyadicInterval 40),(⟨740860903592,740860922921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197053065408,197053065472⟩ : DyadicInterval 40),(⟨-240251286400,-240251286336⟩ : DyadicInterval 40),(⟨740804927797,740804947126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83229929,111098662⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83226752,83226816⟩ : DyadicInterval 40),(⟨-83233088,-83233024⟩ : DyadicInterval 40),(⟨762123380419,762123399748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111092992,111093056⟩ : DyadicInterval 40),(⟨-111104320,-111104256⟩ : DyadicInterval 40),(⟨762123377989,762123397319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11264,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123408512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215640945348,215895743552⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196907774464,196907774528⟩ : DyadicInterval 40),(⟨-240035065600,-240035065536⟩ : DyadicInterval 40),(⟨740839475390,740839494719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197120773632,197120773696⟩ : DyadicInterval 40),(⟨-240352073472,-240352073408⟩ : DyadicInterval 40),(⟨740788816655,740788835985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43231299776,-43127291072⟩ : DyadicInterval 40),(⟨783687029152,783739052768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196997960704,197188462080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240452846464,-240169271552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1074_ok : ecellOkT e1074 = true := by decide +kernel
theorem e1074_pos {a z : ℝ} (ha1 : ((803727/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((25143/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1074 e1074_ok ha1 ha2 hz1 hz2 hz

-- box ['401439/2048000', '803727/4096000', '3997/4000', '1999/2000']  interval_lower 207278653/549755813888
noncomputable def e1075 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549818,0,true,196807426368,196807426432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705734,0,false,-239885769920,-239885769856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451521,0,true,196997960704,196997960768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804031,0,false,-240169271616,-240169271552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314870909126,0,true,196672268672,196672268736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884152346426,0,false,-239684738880,-239684738816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315152577110,0,true,196907777792,196907777856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883870678442,0,false,-240035070528,-240035070464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567052713,0,true,55423488,55423552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456202839,0,false,-55426368,-55426304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594859425,0,true,83228480,83228544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428396127,0,false,-83234816,-83234752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621475,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624983,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314951724826,0,true,196739845696,196739845760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884071530726,0,false,-239785244032,-239785243968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315206523223,0,true,196952877632,196952877696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883816732329,0,false,-240102180096,-240102180032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057198034407,0,false,-43149302464,-43149302400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057297944679,0,false,-43045398272,-43045398208⟩
    { al := (401439/2048000), au := (803727/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨215520922042,215748823745⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196672268672,196672268736⟩ : DyadicInterval 40),(⟨-239684738880,-239684738816⟩ : DyadicInterval 40),(⟨740895404126,740895423455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196907777792,196907777856⟩ : DyadicInterval 40),(⟨-240035070528,-240035070464⟩ : DyadicInterval 40),(⟨740839474588,740839493918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55424937,83231649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55423488,55423552⟩ : DyadicInterval 40),(⟨-55426368,-55426304⟩ : DyadicInterval 40),(⟨762123382198,762123401527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83228480,83228544⟩ : DyadicInterval 40),(⟨-83234816,-83234752⟩ : DyadicInterval 40),(⟨762123380419,762123399748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215440097050,215694895447⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196739845696,196739845760⟩ : DyadicInterval 40),(⟨-239785244032,-239785243968⟩ : DyadicInterval 40),(⟨740879364606,740879383935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196952877632,196952877696⟩ : DyadicInterval 40),(⟨-240102180096,-240102180032⟩ : DyadicInterval 40),(⟨740828754187,740828773516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43149302464,-43045398208⟩ : DyadicInterval 40),(⟨783646082720,783698054112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196807426368,196997960768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240169271616,-239885769856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1075_ok : ecellOkT e1075 = true := by decide +kernel
theorem e1075_pos {a z : ℝ} (ha1 : ((401439/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((803727/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1075 e1075_ok ha1 ha2 hz1 hz2 hz

-- box ['803727/4096000', '25143/128000', '3997/4000', '1999/2000']  interval_lower 104738333/274877906944
noncomputable def e1076 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451520,0,true,196997960704,196997960768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804032,0,false,-240169271616,-240169271552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353223,0,true,197188462016,197188462080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902329,0,false,-240452846464,-240452846400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315098639902,0,true,196862683520,196862683584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883924615650,0,false,-239967976128,-239967976064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315380364861,0,true,197098199488,197098199552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883642890691,0,false,-240318468992,-240318468928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567114710,0,true,55485504,55485568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456140842,0,false,-55488384,-55488320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594952442,0,true,83321472,83321536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428303110,0,false,-83327872,-83327808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621461,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624976,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315179541062,0,true,196930320320,196930320384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883843714490,0,false,-240068613504,-240068613440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315434367945,0,true,197143339136,197143339200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883588887607,0,false,-240385666752,-240385666688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057108593061,0,false,-43242327616,-43242327552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057208620108,0,false,-43138293184,-43138293120⟩
    { al := (803727/4096000), au := (25143/128000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨215748823744,215976725447⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703044,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196862683520,196862683584⟩ : DyadicInterval 40),(⟨-239967976128,-239967976064⟩ : DyadicInterval 40),(⟨740850190483,740850209812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197098199488,197098199552⟩ : DyadicInterval 40),(⟨-240318468992,-240318468928⟩ : DyadicInterval 40),(⟨740794188959,740794208289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55486934,83324666⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55485504,55485568⟩ : DyadicInterval 40),(⟨-55488384,-55488320⟩ : DyadicInterval 40),(⟨762123382191,762123401520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83321472,83321536⟩ : DyadicInterval 40),(⟨-83327872,-83327808⟩ : DyadicInterval 40),(⟨762123380437,762123399766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215667913286,215922740169⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196930320320,196930320384⟩ : DyadicInterval 40),(⟨-240068613504,-240068613440⟩ : DyadicInterval 40),(⟨740834116560,740834135889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197143339136,197143339200⟩ : DyadicInterval 40),(⟨-240385666752,-240385666688⟩ : DyadicInterval 40),(⟨740783445599,740783464929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43242327616,-43138293120⟩ : DyadicInterval 40),(⟨783692530176,783744566688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196997960704,197188462080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240452846464,-240169271552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1076_ok : ecellOkT e1076 = true := by decide +kernel
theorem e1076_pos {a z : ℝ} (ha1 : ((803727/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((25143/128000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1076 e1076_ok ha1 ha2 hz1 hz2 hz

-- box ['40059/204800', '802029/4096000', '1999/2000', '3999/4000']  interval_lower 405013821/1099511627776
noncomputable def e1077 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746414,0,true,196426258560,196426258624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509138,0,false,-239318985728,-239318985664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648117,0,true,196616859008,196616859072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607435,0,false,-239602341312,-239602341248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314469213854,0,true,196336314688,196336314752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884554041698,0,false,-239185313280,-239185313216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314750824863,0,true,196571848128,196571848192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884272430689,0,false,-239535414976,-239535414912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539278333,0,true,27650176,27650240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483977219,0,false,-27650944,-27650880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566992041,0,true,55362816,55362880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456263511,0,false,-55365696,-55365632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624988,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627081,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314522975016,0,true,196381283264,196381283328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884500280536,0,false,-239252141120,-239252141056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1314777745108,0,true,196594360960,196594361024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884245510444,0,false,-239568888320,-239568888256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057366096887,0,false,-42974527296,-42974527232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057465797360,0,false,-42870857792,-42870857728⟩
    { al := (40059/204800), au := (802029/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨215065118638,215293020341⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550360,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196336314688,196336314752⟩ : DyadicInterval 40),(⟨-239185313280,-239185313216⟩ : DyadicInterval 40),(⟨740975037109,740975056439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196571848128,196571848192⟩ : DyadicInterval 40),(⟨-239535414976,-239535414912⟩ : DyadicInterval 40),(⟨740919225880,740919245209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27650557,55364265⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27650176,27650240⟩ : DyadicInterval 40),(⟨-27650944,-27650880⟩ : DyadicInterval 40),(⟨762123383240,762123402569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55362816,55362880⟩ : DyadicInterval 40),(⟨-55365696,-55365632⟩ : DyadicInterval 40),(⟨762123382204,762123401533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215011347240,215266117332⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196381283264,196381283328⟩ : DyadicInterval 40),(⟨-239252141120,-239252141056⟩ : DyadicInterval 40),(⟨740964388231,740964407560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196594360960,196594361024⟩ : DyadicInterval 40),(⟨-239568888320,-239568888256⟩ : DyadicInterval 40),(⟨740913886768,740913906098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42974527296,-42870857728⟩ : DyadicInterval 40),(⟨783558812480,783610666528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196426258560,196616859072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239602341312,-239318985664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1077_ok : ecellOkT e1077 = true := by decide +kernel
theorem e1077_pos {a z : ℝ} (ha1 : ((40059/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((802029/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1077 e1077_ok ha1 ha2 hz1 hz2 hz

-- box ['802029/4096000', '401439/2048000', '1999/2000', '3999/4000']  interval_lower 409370357/1099511627776
noncomputable def e1078 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648116,0,true,196616859008,196616859072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607436,0,false,-239602341312,-239602341248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549819,0,true,196807426368,196807426432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705733,0,false,-239885769920,-239885769856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314697001605,0,true,196526835392,196526835456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884326253947,0,false,-239468492736,-239468492672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1314978669589,0,true,196762375616,196762375680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨884044585963,0,false,-239818755520,-239818755456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539309322,0,true,27681152,27681216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483946230,0,false,-27681920,-27681856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567054029,0,true,55424832,55424896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456201523,0,false,-55427712,-55427648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624981,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627080,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314750819744,0,true,196571843840,196571843904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884272435808,0,false,-239535408640,-239535408576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315005618320,0,true,196784908416,196784908480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨884017637232,0,false,-239852272896,-239852272832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057276822079,0,false,-43067364416,-43067364352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057376639306,0,false,-42963564736,-42963564672⟩
    { al := (802029/4096000), au := (401439/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨215293020340,215520922043⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550361,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196526835392,196526835456⟩ : DyadicInterval 40),(⟨-239468492736,-239468492672⟩ : DyadicInterval 40),(⟨740929898677,740929918006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196762375616,196762375680⟩ : DyadicInterval 40),(⟨-239818755520,-239818755456⟩ : DyadicInterval 40),(⟨740874015512,740874034842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27681546,55426253⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27681152,27681216⟩ : DyadicInterval 40),(⟨-27681920,-27681856⟩ : DyadicInterval 40),(⟨762123383239,762123402568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55424832,55424896⟩ : DyadicInterval 40),(⟨-55427712,-55427648⟩ : DyadicInterval 40),(⟨762123382197,762123401527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215239191968,215493990544⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196571843840,196571843904⟩ : DyadicInterval 40),(⟨-239535408640,-239535408576⟩ : DyadicInterval 40),(⟨740919226911,740919246240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196784908416,196784908480⟩ : DyadicInterval 40),(⟨-239852272896,-239852272832⟩ : DyadicInterval 40),(⟨740868664903,740868684233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43067364416,-42963564672⟩ : DyadicInterval 40),(⟨783605165952,783657085088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196616859008,196807426432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239885769920,-239602341248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1078_ok : ecellOkT e1078 = true := by decide +kernel
theorem e1078_pos {a z : ℝ} (ha1 : ((802029/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((401439/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1078 e1078_ok ha1 ha2 hz1 hz2 hz

-- box ['40059/204800', '802029/4096000', '3999/4000', '1']  interval_lower 404206785/1099511627776
noncomputable def e1079 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314576746414,0,true,196426258560,196426258624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884446509138,0,false,-239318985728,-239318985664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648117,0,true,196616859008,196616859072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607435,0,false,-239602341312,-239602341248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314522980134,0,true,196381287552,196381287616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884500275418,0,false,-239252147456,-239252147392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539310236,0,true,27682048,27682112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483945316,0,false,-27682816,-27682752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627079,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1314549857875,0,true,196403768768,196403768832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨884473397677,0,false,-239285559360,-239285559296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804656641,0,true,196616866112,196616866176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨884218598911,0,false,-239602351872,-239602351808⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057355558565,0,false,-42985485760,-42985485696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057455282727,0,false,-42881790528,-42881790464⟩
    { al := (40059/204800), au := (802029/4096000), zl := (3999/4000), zu := 1,
      A := ⟨215065118638,215293020341⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196426258560,196426258624⟩ : DyadicInterval 40),(⟨-239318985728,-239318985664⟩ : DyadicInterval 40),(⟨740953734584,740953753914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550360,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196381287552,196381287616⟩ : DyadicInterval 40),(⟨-239252147456,-239252147392⟩ : DyadicInterval 40),(⟨740964387202,740964406531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550360,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27682460⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27682048,27682112⟩ : DyadicInterval 40),(⟨-27682816,-27682752⟩ : DyadicInterval 40),(⟨762123383239,762123402568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨215038230099,215293028865⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196403768768,196403768832⟩ : DyadicInterval 40),(⟨-239285559360,-239285559296⟩ : DyadicInterval 40),(⟨740959062301,740959081630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616866112,196616866176⟩ : DyadicInterval 40),(⟨-239602351872,-239602351808⟩ : DyadicInterval 40),(⟨740908548668,740908567998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-42985485760,-42881790464⟩ : DyadicInterval 40),(⟨783564278848,783616145760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨196426258560,196616859072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239602341312,-239318985664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1079_ok : ecellOkT e1079 = true := by decide +kernel
theorem e1079_pos {a z : ℝ} (ha1 : ((40059/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((802029/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1079 e1079_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B017

end


