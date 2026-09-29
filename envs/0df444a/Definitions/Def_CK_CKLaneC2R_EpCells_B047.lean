-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B047
-- name    : CK_CKLaneC2R_EpCells_B047
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:25:58.243888+00:00
-- url     : https://prove2.me/theorems/a26b4bc7-1182-4b0f-93e3-7abf1ae5a798
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B047` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B047` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B047` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B047 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B047.lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B047_part00

namespace CKLaneC2R.EpCells.B047

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['683169/4096000', '1367187/8192000', '3997/4000', '1599/1600']  interval_lower 300685603/1099511627776
noncomputable def e2863 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283399180369,0,true,170035142464,170035142528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915624075183,0,false,-201227673984,-201227673920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283536097302,0,true,170152435456,170152435520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915487158250,0,false,-201392100608,-201392100544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535098054,0,true,23470016,23470080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488157498,0,false,-23470592,-23470528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546856646,0,true,35228288,35228352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476398906,0,false,-35229440,-35229376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626647,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627276,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283433667550,0,true,170064687872,170064687936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915589588002,0,false,-201269088064,-201269088000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283559114653,0,true,170172152576,170172152640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915464140899,0,false,-201419745088,-201419745024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068703879526,0,false,-31247592512,-31247592448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068745862449,0,false,-31204400192,-31204400128⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170035142464,170035142528⟩ : DyadicInterval 40),(⟨-201227673984,-201227673920⟩ : DyadicInterval 40),(⟨746673769959,746673789288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170152435456,170152435520⟩ : DyadicInterval 40),(⟨-201392100608,-201392100544⟩ : DyadicInterval 40),(⟨746650645377,746650664707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23470278,35228870⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23470016,23470080⟩ : DyadicInterval 40),(⟨-23470592,-23470528⟩ : DyadicInterval 40),(⟨762123383338,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35228288,35228352⟩ : DyadicInterval 40),(⟨-35229440,-35229376⟩ : DyadicInterval 40),(⟨762123382999,762123402328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183922039774,184047486877⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170064687872,170064687936⟩ : DyadicInterval 40),(⟨-201269088064,-201269088000⟩ : DyadicInterval 40),(⟨746667946883,746667966213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170172152576,170172152640⟩ : DyadicInterval 40),(⟨-201419745088,-201419745024⟩ : DyadicInterval 40),(⟨746646756137,746646775466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31247592512,-31204400128⟩ : DyadicInterval 40),(⟨777725583680,777747199136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2863_ok : ecellOkT e2863 = true := by decide +kernel
theorem e2863_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2863 e2863_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '3999/4000', '7999/8000']  interval_lower 75668109/274877906944
noncomputable def e2864 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283080407847,0,true,169762010304,169762010368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915942847705,0,false,-200844948032,-200844947968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283217296291,0,true,169879308032,169879308096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915805959261,0,false,-201009283264,-201009283200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523340104,0,true,11712256,11712320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499915448,0,false,-11712448,-11712384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535068407,0,true,23440320,23440384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488187145,0,false,-23440896,-23440832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627276,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283103354947,0,true,169781674176,169781674240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915919900605,0,false,-200872494400,-200872494336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283228787822,0,true,169889154368,169889154432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915794467730,0,false,-201023080000,-201023079936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068814367244,0,false,-31133925632,-31133925568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068856270039,0,false,-31090820160,-31090820096⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169762010304,169762010368⟩ : DyadicInterval 40),(⟨-200844948032,-200844947968⟩ : DyadicInterval 40),(⟨746727541018,746727560347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169879308032,169879308096⟩ : DyadicInterval 40),(⟨-201009283264,-201009283200⟩ : DyadicInterval 40),(⟨746704462090,746704481420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11712328,23440631⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11712256,11712320⟩ : DyadicInterval 40),(⟨-11712448,-11712384⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23440320,23440384⟩ : DyadicInterval 40),(⟨-23440896,-23440832⟩ : DyadicInterval 40),(⟨762123383340,762123402669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183591727171,183717160046⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169781674176,169781674240⟩ : DyadicInterval 40),(⟨-200872494400,-200872494336⟩ : DyadicInterval 40),(⟨746723673451,746723692781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169889154368,169889154432⟩ : DyadicInterval 40),(⟨-201023080000,-201023079936⟩ : DyadicInterval 40),(⟨746702523864,746702543193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31133925632,-31090820096⟩ : DyadicInterval 40),(⟨777668793664,777690365696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2864_ok : ecellOkT e2864 = true := by decide +kernel
theorem e2864_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2864 e2864_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '3999/4000', '7999/8000']  interval_lower 152033769/549755813888
noncomputable def e2865 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283194330210,0,true,169859629568,169859629632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915828925342,0,false,-200981710656,-200981710592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283331232898,0,true,169976929088,169976929152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915692022654,0,false,-201146083392,-201146083328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523347675,0,true,11719808,11719872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499907877,0,false,-11720000,-11719936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535083549,0,true,23455488,23455552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488172003,0,false,-23456064,-23456000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627275,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283217291549,0,true,169879303936,169879304000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915805964003,0,false,-201009277568,-201009277504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283342731552,0,true,169986780672,169986780736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915680524000,0,false,-201159890432,-201159890368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068776277769,0,false,-31173109760,-31173109696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068818208944,0,false,-31129973568,-31129973504⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169859629568,169859629632⟩ : DyadicInterval 40),(⟨-200981710656,-200981710592⟩ : DyadicInterval 40),(⟨746708335337,746708354666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169976929088,169976929152⟩ : DyadicInterval 40),(⟨-201146083392,-201146083328⟩ : DyadicInterval 40),(⟨746685239396,746685258725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11719899,23455773⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11719808,11719872⟩ : DyadicInterval 40),(⟨-11720000,-11719936⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23455488,23455552⟩ : DyadicInterval 40),(⟨-23456064,-23456000⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183705663773,183831103776⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169879303936,169879304000⟩ : DyadicInterval 40),(⟨-201009277568,-201009277504⟩ : DyadicInterval 40),(⟨746704462908,746704482237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169986780672,169986780736⟩ : DyadicInterval 40),(⟨-201159890432,-201159890368⟩ : DyadicInterval 40),(⟨746683298745,746683318074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31173109760,-31129973504⟩ : DyadicInterval 40),(⟨777688370368,777709957760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2865_ok : ecellOkT e2865 = true := by decide +kernel
theorem e2865_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2865 e2865_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '7999/8000', '1']  interval_lower 302473201/1099511627776
noncomputable def e2866 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283103359682,0,true,169781678272,169781678336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915919895870,0,false,-200872500096,-200872500032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523348250,0,true,11720384,11720448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499907302,0,false,-11720576,-11720512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283114830821,0,true,169791508032,169791508096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915908424731,0,false,-200886270656,-200886270592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240270845,0,true,169898993344,169898993408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915782984707,0,false,-201036866688,-201036866624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068810529732,0,false,-31137873344,-31137873280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068852437535,0,false,-31094762624,-31094762560⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (7999/8000), zu := 1,
      A := ⟨183614683742,183728634594⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169781678272,169781678336⟩ : DyadicInterval 40),(⟨-200872500096,-200872500032⟩ : DyadicInterval 40),(⟨746723672636,746723691965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11720474⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11720384,11720448⟩ : DyadicInterval 40),(⟨-11720576,-11720512⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183603203045,183728643069⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169791508032,169791508096⟩ : DyadicInterval 40),(⟨-200886270656,-200886270592⟩ : DyadicInterval 40),(⟨746721739066,746721758396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898993344,169898993408⟩ : DyadicInterval 40),(⟨-201036866688,-201036866624⟩ : DyadicInterval 40),(⟨746700586936,746700606265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31137873344,-31094762560⟩ : DyadicInterval 40),(⟨777670764896,777692339552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2866_ok : ecellOkT e2866 = true := by decide +kernel
theorem e2866_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2866 e2866_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '7999/8000', '1']  interval_lower 151933845/549755813888
noncomputable def e2867 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283217296289,0,true,169879308032,169879308096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915805959263,0,false,-201009283264,-201009283200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523355821,0,true,11727936,11728000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499899731,0,false,-11728128,-11728064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283228774548,0,true,169889142976,169889143040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915794481004,0,false,-201023064064,-201023064000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354221696,0,true,169996624896,169996624960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915669033856,0,false,-201173687424,-201173687360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068772435496,0,false,-31177062528,-31177062464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068814371681,0,false,-31133921024,-31133920960⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (7999/8000), zu := 1,
      A := ⟨183728634593,183842585445⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169879308032,169879308096⟩ : DyadicInterval 40),(⟨-201009283264,-201009283200⟩ : DyadicInterval 40),(⟨746704462091,746704481420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11728045⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11727936,11728000⟩ : DyadicInterval 40),(⟨-11728128,-11728064⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183717146772,183842593920⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169889142976,169889143040⟩ : DyadicInterval 40),(⟨-201023064064,-201023064000⟩ : DyadicInterval 40),(⟨746702526114,746702545443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996624896,169996624960⟩ : DyadicInterval 40),(⟨-201173687424,-201173687360⟩ : DyadicInterval 40),(⟨746681359394,746681378724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31177062528,-31133920960⟩ : DyadicInterval 40),(⟨777690344096,777711934144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2867_ok : ecellOkT e2867 = true := by decide +kernel
theorem e2867_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2867 e2867_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '3999/4000', '7999/8000']  interval_lower 305465659/1099511627776
noncomputable def e2868 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283308252573,0,true,169957240192,169957240256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915715002979,0,false,-201118490304,-201118490240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283445169506,0,true,170074541504,170074541568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915578086046,0,false,-201282900608,-201282900544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523355245,0,true,11727360,11727424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499900307,0,false,-11727552,-11727488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535098693,0,true,23470656,23470720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488156859,0,false,-23471168,-23471104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627274,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283331228154,0,true,169976924992,169976925056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915692027398,0,false,-201146077696,-201146077632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283456675282,0,true,170084398336,170084398400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915566580270,0,false,-201296717888,-201296717824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068738164679,0,false,-31212319552,-31212319488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068780124235,0,false,-31169152640,-31169152576⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169957240192,169957240256⟩ : DyadicInterval 40),(⟨-201118490304,-201118490240⟩ : DyadicInterval 40),(⟨746689117502,746689136831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170074541504,170074541568⟩ : DyadicInterval 40),(⟨-201282900608,-201282900544⟩ : DyadicInterval 40),(⟨746666004567,746666023896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11727469,23470917⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11727360,11727424⟩ : DyadicInterval 40),(⟨-11727552,-11727488⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23470656,23470720⟩ : DyadicInterval 40),(⟨-23471168,-23471104⟩ : DyadicInterval 40),(⟨762123383306,762123402635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183819600378,183945047506⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169976924992,169976925056⟩ : DyadicInterval 40),(⟨-201146077696,-201146077632⟩ : DyadicInterval 40),(⟨746685240215,746685259544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170084398336,170084398400⟩ : DyadicInterval 40),(⟨-201296717888,-201296717824⟩ : DyadicInterval 40),(⟨746664061462,746664080791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31212319552,-31169152576⟩ : DyadicInterval 40),(⟨777707959904,777729562656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2868_ok : ecellOkT e2868 = true := by decide +kernel
theorem e2868_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2868 e2868_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '3999/4000', '7999/8000']  interval_lower 306867463/1099511627776
noncomputable def e2869 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283422174936,0,true,170054842176,170054842240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915601080616,0,false,-201255286912,-201255286848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283559106113,0,true,170172145280,170172145344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915464149439,0,false,-201419734848,-201419734784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523362817,0,true,11734976,11735040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499892735,0,false,-11735104,-11735040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535113836,0,true,23485760,23485824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488141716,0,false,-23486336,-23486272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627274,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283445164764,0,true,170074537472,170074537536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915578090788,0,false,-201282894912,-201282894848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283570619015,0,true,170182007296,170182007360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915452636537,0,false,-201433562432,-201433562368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068700027971,0,false,-31251555072,-31251555008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068742015910,0,false,-31208357440,-31208357376⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170054842176,170054842240⟩ : DyadicInterval 40),(⟨-201255286912,-201255286848⟩ : DyadicInterval 40),(⟨746669887486,746669906815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170172145280,170172145344⟩ : DyadicInterval 40),(⟨-201419734848,-201419734784⟩ : DyadicInterval 40),(⟨746646757576,746646776905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11735041,23486060⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11734976,11735040⟩ : DyadicInterval 40),(⟨-11735104,-11735040⟩ : DyadicInterval 40),(⟨762123383490,762123402819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23485760,23485824⟩ : DyadicInterval 40),(⟨-23486336,-23486272⟩ : DyadicInterval 40),(⟨762123383338,762123402667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183933536988,184058991239⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170074537472,170074537536⟩ : DyadicInterval 40),(⟨-201282894912,-201282894848⟩ : DyadicInterval 40),(⟨746666005349,746666024679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170182007296,170182007360⟩ : DyadicInterval 40),(⟨-201433562432,-201433562368⟩ : DyadicInterval 40),(⟨746644812077,746644831406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31251555072,-31208357376⟩ : DyadicInterval 40),(⟨777727562304,777749180416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2869_ok : ecellOkT e2869 = true := by decide +kernel
theorem e2869_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2869 e2869_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '7999/8000', '1']  interval_lower 76316337/274877906944
noncomputable def e2870 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283331232896,0,true,169976929088,169976929152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915692022656,0,false,-201146083392,-201146083328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523363393,0,true,11735552,11735616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499892159,0,false,-11735680,-11735616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283342718275,0,true,169986769280,169986769344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915680537277,0,false,-201159874496,-201159874432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468172550,0,true,170094247744,170094247808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915555083002,0,false,-201310525184,-201310525120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068734317640,0,false,-31216277376,-31216277312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068776282210,0,false,-31173105152,-31173105088⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (7999/8000), zu := 1,
      A := ⟨183842585444,183956536296⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169976929088,169976929152⟩ : DyadicInterval 40),(⟨-201146083392,-201146083328⟩ : DyadicInterval 40),(⟨746685239396,746685258725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11735617⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11735552,11735616⟩ : DyadicInterval 40),(⟨-11735680,-11735616⟩ : DyadicInterval 40),(⟨762123383490,762123402819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183831090499,183956544774⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169986769280,169986769344⟩ : DyadicInterval 40),(⟨-201159874496,-201159874432⟩ : DyadicInterval 40),(⟨746683300998,746683320328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094247744,170094247808⟩ : DyadicInterval 40),(⟨-201310525184,-201310525120⟩ : DyadicInterval 40),(⟨746662119723,746662139052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31216277376,-31173105088⟩ : DyadicInterval 40),(⟨777709936160,777731541568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2870_ok : ecellOkT e2870 = true := by decide +kernel
theorem e2870_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2870 e2870_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '7999/8000', '1']  interval_lower 153333307/549755813888
noncomputable def e2871 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283445169503,0,true,170074541504,170074541568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915578086049,0,false,-201282900608,-201282900544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523370965,0,true,11743104,11743168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499884587,0,false,-11743296,-11743232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283456662002,0,true,170084386944,170084387008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915566593550,0,false,-201296701952,-201296701888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582123407,0,true,170191861952,170191862016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915441132145,0,false,-201447379968,-201447379904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068696176164,0,false,-31255517952,-31255517888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068738169123,0,false,-31212315008,-31212314944⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (7999/8000), zu := 1,
      A := ⟨183956536295,184070487147⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170074541504,170074541568⟩ : DyadicInterval 40),(⟨-201282900608,-201282900544⟩ : DyadicInterval 40),(⟨746666004567,746666023897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11743189⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11743104,11743168⟩ : DyadicInterval 40),(⟨-11743296,-11743232⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183945034226,184070495631⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170084386944,170084387008⟩ : DyadicInterval 40),(⟨-201296701952,-201296701888⟩ : DyadicInterval 40),(⟨746664063719,746664083048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191861952,170191862016⟩ : DyadicInterval 40),(⟨-201447379968,-201447379904⟩ : DyadicInterval 40),(⟨746642867882,746642887211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31255517952,-31212314944⟩ : DyadicInterval 40),(⟨777729541088,777751161856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2871_ok : ecellOkT e2871 = true := by decide +kernel
theorem e2871_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2871 e2871_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '999/1000', '7993/8000']  interval_lower 154739359/549755813888
noncomputable def e2872 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283398044434,0,true,170034169280,170034169344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915625211118,0,false,-201226309888,-201226309824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283534904391,0,true,170151413568,170151413632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915488351161,0,false,-201390667904,-201390667840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593826329,0,true,82195456,82195520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429429223,0,false,-82201664,-82201600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605630356,0,true,93998528,93998592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417625196,0,false,-94006656,-94006592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619739,0,false,-8064,-8000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621631,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283490075817,0,true,170113011520,170113011584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915533179735,0,false,-201336829632,-201336829568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283615494280,0,true,170220446976,170220447040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915407761272,0,false,-201487461504,-201487461440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068685001840,0,false,-31267014528,-31267014464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068726988043,0,false,-31223818112,-31223818048⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170034169280,170034169344⟩ : DyadicInterval 40),(⟨-201226309888,-201226309824⟩ : DyadicInterval 40),(⟨746673961731,746673981061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170151413568,170151413632⟩ : DyadicInterval 40),(⟨-201390667904,-201390667840⟩ : DyadicInterval 40),(⟨746650846932,746650866262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82198553,94002580⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82195456,82195520⟩ : DyadicInterval 40),(⟨-82201664,-82201600⟩ : DyadicInterval 40),(⟨762123380510,762123399840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93998528,93998592⟩ : DyadicInterval 40),(⟨-94006656,-94006592⟩ : DyadicInterval 40),(⟨762123379578,762123398908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8064,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183978448041,184103866504⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170113011520,170113011584⟩ : DyadicInterval 40),(⟨-201336829632,-201336829568⟩ : DyadicInterval 40),(⟨746658420124,746658439453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170220446976,170220447040⟩ : DyadicInterval 40),(⟨-201487461504,-201487461440⟩ : DyadicInterval 40),(⟨746637227579,746637246909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31267014528,-31223818048⟩ : DyadicInterval 40),(⟨777735292640,777756910144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2872_ok : ecellOkT e2872 = true := by decide +kernel
theorem e2872_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2872 e2872_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '999/1000', '7993/8000']  interval_lower 310888993/1099511627776
noncomputable def e2873 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283511881334,0,true,170131691200,170131691264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915511374218,0,false,-201363017344,-201363017280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283648755535,0,true,170248937280,170248937344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915374500017,0,false,-201527412928,-201527412864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593879334,0,true,82248448,82248512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429376218,0,false,-82254656,-82254592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605690939,0,true,94059136,94059200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417564613,0,false,-94067200,-94067136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619728,0,false,-8064,-8000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621623,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283603969687,0,true,170210575232,170210575296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915419285865,0,false,-201473619264,-201473619200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283729395273,0,true,170318007232,170318007296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915293860279,0,false,-201624278464,-201624278400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068646846536,0,false,-31306271168,-31306271104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068688861110,0,false,-31263043968,-31263043904⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170131691200,170131691264⟩ : DyadicInterval 40),(⟨-201363017344,-201363017280⟩ : DyadicInterval 40),(⟨746654736626,746654755955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170248937280,170248937344⟩ : DyadicInterval 40),(⟨-201527412928,-201527412864⟩ : DyadicInterval 40),(⟨746631604855,746631624185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82251558,94063163⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82248448,82248512⟩ : DyadicInterval 40),(⟨-82254656,-82254592⟩ : DyadicInterval 40),(⟨762123380502,762123399832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94059136,94059200⟩ : DyadicInterval 40),(⟨-94067200,-94067136⟩ : DyadicInterval 40),(⟨762123379536,762123398866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8064,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184092341911,184217767497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170210575232,170210575296⟩ : DyadicInterval 40),(⟨-201473619264,-201473619200⟩ : DyadicInterval 40),(⟨746639175598,746639194927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170318007232,170318007296⟩ : DyadicInterval 40),(⟨-201624278464,-201624278400⟩ : DyadicInterval 40),(⟨746617968508,746617987837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31306271168,-31263043904⟩ : DyadicInterval 40),(⟨777754905568,777776538464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2873_ok : ecellOkT e2873 = true := by decide +kernel
theorem e2873_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2873 e2873_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '7993/8000', '3997/4000']  interval_lower 154638855/549755813888
noncomputable def e2874 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283421053245,0,true,170053881216,170053881280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915602202307,0,false,-201253939968,-201253939904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283557927446,0,true,170171135616,170171135680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915465328106,0,false,-201418319232,-201418319168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582083824,0,true,70453760,70453824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441171728,0,false,-70458368,-70458304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593880280,0,true,82249408,82249472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429375272,0,false,-82255616,-82255552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621622,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623262,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283501580002,0,true,170122866624,170122866688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915521675550,0,false,-201350645696,-201350645632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283627005618,0,true,170230307200,170230307264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915396249934,0,false,-201501288064,-201501288000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068681146768,0,false,-31270980800,-31270980736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068723137992,0,false,-31227779072,-31227779008⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170053881216,170053881280⟩ : DyadicInterval 40),(⟨-201253939968,-201253939904⟩ : DyadicInterval 40),(⟨746670076909,746670096239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170171135616,170171135680⟩ : DyadicInterval 40),(⟨-201418319232,-201418319168⟩ : DyadicInterval 40),(⟨746646956754,746646976084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70456048,82252504⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70453760,70453824⟩ : DyadicInterval 40),(⟨-70458368,-70458304⟩ : DyadicInterval 40),(⟨762123381341,762123400670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82249408,82249472⟩ : DyadicInterval 40),(⟨-82255616,-82255552⟩ : DyadicInterval 40),(⟨762123380502,762123399832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183989952226,184115377842⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170122866624,170122866688⟩ : DyadicInterval 40),(⟨-201350645696,-201350645632⟩ : DyadicInterval 40),(⟨746656476824,746656496153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170230307200,170230307264⟩ : DyadicInterval 40),(⟨-201501288064,-201501288000⟩ : DyadicInterval 40),(⟨746635281750,746635301079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31270980800,-31227779008⟩ : DyadicInterval 40),(⟨777737273120,777758893280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2874_ok : ecellOkT e2874 = true := by decide +kernel
theorem e2874_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2874 e2874_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '7993/8000', '3997/4000']  interval_lower 310687797/1099511627776
noncomputable def e2875 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283534904389,0,true,170151413568,170151413632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915488351163,0,false,-201390667904,-201390667840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283671792834,0,true,170268669760,170268669824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915351462718,0,false,-201555084736,-201555084672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582129259,0,true,70499200,70499264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441126293,0,false,-70503744,-70503680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593933291,0,true,82302400,82302464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429322261,0,false,-82308608,-82308544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621614,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623256,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283615480997,0,true,170220435584,170220435648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915407774555,0,false,-201487445568,-201487445504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283740913735,0,true,170327872768,170327872832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915282341817,0,false,-201638115264,-201638115200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068642986692,0,false,-31310242496,-31310242432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068685006289,0,false,-31267009984,-31267009920⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170151413568,170151413632⟩ : DyadicInterval 40),(⟨-201390667904,-201390667840⟩ : DyadicInterval 40),(⟨746650846933,746650866262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170268669760,170268669824⟩ : DyadicInterval 40),(⟨-201555084736,-201555084672⟩ : DyadicInterval 40),(⟨746627709798,746627729128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70501483,82305515⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70499200,70499264⟩ : DyadicInterval 40),(⟨-70503744,-70503680⟩ : DyadicInterval 40),(⟨762123381303,762123400632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82302400,82302464⟩ : DyadicInterval 40),(⟨-82308608,-82308544⟩ : DyadicInterval 40),(⟨762123380494,762123399824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184103853221,184229285959⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170220435584,170220435648⟩ : DyadicInterval 40),(⟨-201487445568,-201487445504⟩ : DyadicInterval 40),(⟨746637229840,746637249170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170327872768,170327872832⟩ : DyadicInterval 40),(⟨-201638115264,-201638115200⟩ : DyadicInterval 40),(⟨746616020181,746616039511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31310242496,-31267009920⟩ : DyadicInterval 40),(⟨777756888576,777778524128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2875_ok : ecellOkT e2875 = true := by decide +kernel
theorem e2875_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2875 e2875_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '999/1000', '7993/8000']  interval_lower 312302807/1099511627776
noncomputable def e2876 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283625718235,0,true,170229204480,170229204544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915397537317,0,false,-201499741760,-201499741696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283762606679,0,true,170346452416,170346452480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915260648873,0,false,-201664174912,-201664174848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593932345,0,true,82301440,82301504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429323207,0,false,-82307712,-82307648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605751527,0,true,94119680,94119744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417504025,0,false,-94127808,-94127744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619718,0,false,-8064,-8000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621616,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283717863561,0,true,170308130304,170308130368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915305391991,0,false,-201610425856,-201610425792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283843296279,0,true,170415558912,170415558976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915179959273,0,false,-201761112384,-201761112320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068608667630,0,false,-31345553472,-31345553408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068650710579,0,false,-31302295488,-31302295424⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170229204480,170229204544⟩ : DyadicInterval 40),(⟨-201499741760,-201499741696⟩ : DyadicInterval 40),(⟨746635499373,746635518702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170346452416,170346452480⟩ : DyadicInterval 40),(⟨-201664174912,-201664174848⟩ : DyadicInterval 40),(⟨746612350586,746612369916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82304569,94123751⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82301440,82301504⟩ : DyadicInterval 40),(⟨-82307712,-82307648⟩ : DyadicInterval 40),(⟨762123380526,762123399856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94119680,94119744⟩ : DyadicInterval 40),(⟨-94127808,-94127744⟩ : DyadicInterval 40),(⟨762123379558,762123398887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8064,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184206235785,184331668503⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170308130304,170308130368⟩ : DyadicInterval 40),(⟨-201610425856,-201610425792⟩ : DyadicInterval 40),(⟨746619918898,746619938228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170415558912,170415558976⟩ : DyadicInterval 40),(⟨-201761112384,-201761112320⟩ : DyadicInterval 40),(⟨746598697221,746598716550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31345553472,-31302295424⟩ : DyadicInterval 40),(⟨777774531328,777796179616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2876_ok : ecellOkT e2876 = true := by decide +kernel
theorem e2876_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2876 e2876_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '999/1000', '7993/8000']  interval_lower 39214961/137438953472
noncomputable def e2877 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283739555135,0,true,170326709120,170326709184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915283700417,0,false,-201636483200,-201636483136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283876457823,0,true,170443958784,170443958848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915146797729,0,false,-201800953920,-201800953856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593985359,0,true,82354496,82354560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429270193,0,false,-82360704,-82360640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605812120,0,true,94180288,94180352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417443432,0,false,-94188416,-94188352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619708,0,false,-8128,-8064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621608,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283831757440,0,true,170405676736,170405676800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915191498112,0,false,-201747249536,-201747249472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283957197276,0,true,170513101888,170513101952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915066058276,0,false,-201897963328,-201897963264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068570465128,0,false,-31384861440,-31384861376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068612536452,0,false,-31341572736,-31341572672⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170326709120,170326709184⟩ : DyadicInterval 40),(⟨-201636483200,-201636483136⟩ : DyadicInterval 40),(⟨746616249998,746616269327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170443958784,170443958848⟩ : DyadicInterval 40),(⟨-201800953920,-201800953856⟩ : DyadicInterval 40),(⟨746593084262,746593103592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82357583,94184344⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82354496,82354560⟩ : DyadicInterval 40),(⟨-82360704,-82360640⟩ : DyadicInterval 40),(⟨762123380486,762123399816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94180288,94180352⟩ : DyadicInterval 40),(⟨-94188416,-94188352⟩ : DyadicInterval 40),(⟨762123379547,762123398877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8128,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184320129664,184445569500⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170405676736,170405676800⟩ : DyadicInterval 40),(⟨-201747249536,-201747249472⟩ : DyadicInterval 40),(⟨746600650077,746600669407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170513101888,170513101952⟩ : DyadicInterval 40),(⟨-201897963328,-201897963264⟩ : DyadicInterval 40),(⟨746579413820,746579433150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31384861440,-31341572672⟩ : DyadicInterval 40),(⟨777794169952,777815833600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2877_ok : ecellOkT e2877 = true := by decide +kernel
theorem e2877_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2877 e2877_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '7993/8000', '3997/4000']  interval_lower 78025295/274877906944
noncomputable def e2878 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283648755533,0,true,170248937280,170248937344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915374500019,0,false,-201527412928,-201527412864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283785658222,0,true,170366195328,170366195392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915237597330,0,false,-201691867328,-201691867264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582174696,0,true,70544640,70544704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441080856,0,false,-70549184,-70549120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593986306,0,true,82355392,82355456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429269246,0,false,-82361664,-82361600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621606,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623250,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283729381987,0,true,170317995904,170317995968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915293873565,0,false,-201624262464,-201624262400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283854821858,0,true,170425429632,170425429696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915168433694,0,false,-201774959488,-201774959424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068604803013,0,false,-31349529856,-31349529792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068646850989,0,false,-31306266560,-31306266496⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170248937280,170248937344⟩ : DyadicInterval 40),(⟨-201527412928,-201527412864⟩ : DyadicInterval 40),(⟨746631604856,746631624185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170366195328,170366195392⟩ : DyadicInterval 40),(⟨-201691867328,-201691867264⟩ : DyadicInterval 40),(⟨746608450697,746608470027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70546920,82358530⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70544640,70544704⟩ : DyadicInterval 40),(⟨-70549184,-70549120⟩ : DyadicInterval 40),(⟨762123381297,762123400626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82355392,82355456⟩ : DyadicInterval 40),(⟨-82361664,-82361600⟩ : DyadicInterval 40),(⟨762123380518,762123399848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184217754211,184343194082⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170317995904,170317995968⟩ : DyadicInterval 40),(⟨-201624262464,-201624262400⟩ : DyadicInterval 40),(⟨746617970709,746617990038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170425429632,170425429696⟩ : DyadicInterval 40),(⟨-201774959488,-201774959424⟩ : DyadicInterval 40),(⟨746596746495,746596765825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31349529856,-31306266496⟩ : DyadicInterval 40),(⟨777776516864,777798167808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2878_ok : ecellOkT e2878 = true := by decide +kernel
theorem e2878_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2878 e2878_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '7993/8000', '3997/4000']  interval_lower 156758723/549755813888
noncomputable def e2879 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283762606677,0,true,170346452416,170346452480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915260648875,0,false,-201664174912,-201664174848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283899523610,0,true,170463712192,170463712256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915123731942,0,false,-201828666880,-201828666816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582220137,0,true,70590080,70590144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441035415,0,false,-70594688,-70594624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594039325,0,true,82408448,82408512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429216227,0,false,-82414656,-82414592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621599,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623244,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283843282991,0,true,170415547520,170415547584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915179972561,0,false,-201761096448,-201761096384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283968729981,0,true,170522977856,170522977920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915054525571,0,false,-201911820736,-201911820672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068566595732,0,false,-31388842880,-31388842816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068608672086,0,false,-31345548864,-31345548800⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170346452416,170346452480⟩ : DyadicInterval 40),(⟨-201664174912,-201664174848⟩ : DyadicInterval 40),(⟨746612350587,746612369916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170463712192,170463712256⟩ : DyadicInterval 40),(⟨-201828666880,-201828666816⟩ : DyadicInterval 40),(⟨746589179472,746589198801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70592361,82411549⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70590080,70590144⟩ : DyadicInterval 40),(⟨-70594688,-70594624⟩ : DyadicInterval 40),(⟨762123381323,762123400652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82408448,82408512⟩ : DyadicInterval 40),(⟨-82414656,-82414592⟩ : DyadicInterval 40),(⟨762123380478,762123399808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184331655215,184457102205⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170415547520,170415547584⟩ : DyadicInterval 40),(⟨-201761096448,-201761096384⟩ : DyadicInterval 40),(⟨746598699488,746598718818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170522977856,170522977920⟩ : DyadicInterval 40),(⟨-201911820736,-201911820672⟩ : DyadicInterval 40),(⟨746577460654,746577479984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31388842880,-31345548800⟩ : DyadicInterval 40),(⟨777796158016,777817824320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2879_ok : ecellOkT e2879 = true := by decide +kernel
theorem e2879_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2879 e2879_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B047


