-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0150__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0150__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:27:52.038097+00:00
-- url     : https://prove2.me/theorems/f89e81ab-de60-4be0-b333-b99a81411560
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0150 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0151, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0152, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0153).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0145Logs__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0151Logs__5

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (997 / 25600) (127 / 3200) m) :
    let h := H (2*m)/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (1-4*m) = Real.log 2 * H (2*m) := by
    rw [show 1-4*m = 1-2*(2*m) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hm.1]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * (H (2*m)/2) = biasE (1-4*m)/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (997 / 12800) (127 / 1600) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-127 / 1600) (-997 / 12800) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1473 / 1600) (11803 / 12800) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1473 / 1600) (11803 / 12800) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (997 / 6400) (127 / 800) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-127 / 800) (-997 / 6400) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (673 / 800) (5403 / 6400) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (673 / 800) (5403 / 6400) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(11803 / 12800)
  have hx9 : Bounds (24603 / 12800) (24603 / 12800) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11803 / 12800) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(11803 / 12800)
  have hx10 : Bounds (24603 / 12800) (24603 / 12800) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11803 / 12800) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (130684643 / 200000000) (40838951 / 62500000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (627975443697 / 500000000000) (1255950889317 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(11803 / 12800)
  have hx13 : Bounds (-11803 / 12800) (-11803 / 12800) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11803 / 12800) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (997 / 12800) (997 / 12800) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(11803 / 12800)
  have hx15 : Bounds (997 / 12800) (997 / 12800) x15 := by
    exact hx14
  let x16 : ℝ := -(11803 / 12800)
  have hx16 : Bounds (-11803 / 12800) (-11803 / 12800) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11803 / 12800) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (997 / 12800) (997 / 12800) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(11803 / 12800)
  have hx18 : Bounds (997 / 12800) (997 / 12800) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1276224841 / 500000000) (-1276224839 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-198811901013 / 1000000000000) (-1988119007 / 10000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1057138986381 / 1000000000000) (1057138988617 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (52856949319 / 100000000000) (528569494309 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (52856949319 / 100000000000) (528569494309 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-528569494309 / 1000000000000) (-52856949319 / 100000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (164577685691 / 1000000000000) (16457768781 / 100000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (164577685691 / 1000000000000) (16457768781 / 100000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (11803 / 12800)
  have hx28 : Bounds (164577685691 / 1000000000000) (16457768781 / 100000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1473 / 1600)
  have hx30 : Bounds (3073 / 1600) (3073 / 1600) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1473 / 1600) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1473 / 1600)
  have hx31 : Bounds (3073 / 1600) (3073 / 1600) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1473 / 1600) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (652650653 / 1000000000) (326325327 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (626748580209 / 500000000000) (1253497162339 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1473 / 1600)
  have hx34 : Bounds (-1473 / 1600) (-1473 / 1600) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1473 / 1600) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (127 / 1600) (127 / 1600) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1473 / 1600)
  have hx36 : Bounds (127 / 1600) (127 / 1600) x36 := by
    exact hx35
  let x37 : ℝ := -(1473 / 1600)
  have hx37 : Bounds (-1473 / 1600) (-1473 / 1600) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1473 / 1600) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (127 / 1600) (127 / 1600) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1473 / 1600)
  have hx39 : Bounds (127 / 1600) (127 / 1600) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-158348239 / 62500000) (-126678591 / 50000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-20110226353 / 100000000000) (-50275565803 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (131549362111 / 125000000000) (1052394899127 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (131549362111 / 250000000000) (131549362391 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (131549362111 / 250000000000) (131549362391 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-131549362391 / 250000000000) (-131549362111 / 250000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (41737432609 / 250000000000) (41737433139 / 250000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (41737432609 / 250000000000) (41737433139 / 250000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1473 / 1600)
  have hx49 : Bounds (41737432609 / 250000000000) (41737433139 / 250000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (164577685691 / 1000000000000) (41737433139 / 250000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(5403 / 6400)
  have hx52 : Bounds (11803 / 6400) (11803 / 6400) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5403 / 6400) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(5403 / 6400)
  have hx53 : Bounds (11803 / 6400) (11803 / 6400) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5403 / 6400) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (306027873 / 500000000) (612055747 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (564382341409 / 500000000000) (1128764684663 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(5403 / 6400)
  have hx56 : Bounds (-5403 / 6400) (-5403 / 6400) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5403 / 6400) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (997 / 6400) (997 / 6400) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(5403 / 6400)
  have hx58 : Bounds (997 / 6400) (997 / 6400) x58 := by
    exact hx57
  let x59 : ℝ := -(5403 / 6400)
  have hx59 : Bounds (-5403 / 6400) (-5403 / 6400) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5403 / 6400) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (997 / 6400) (997 / 6400) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(5403 / 6400)
  have hx61 : Bounds (997 / 6400) (997 / 6400) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1859302501 / 1000000000) (-929651249 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-144822233867 / 500000000000) (-144822233633 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (209780053771 / 250000000000) (839120217397 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (209780053771 / 500000000000) (419560108699 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (209780053771 / 500000000000) (419560108699 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-419560108699 / 1000000000000) (-209780053771 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (273587071301 / 1000000000000) (136793536729 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (273587071301 / 1000000000000) (136793536729 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (5403 / 6400)
  have hx71 : Bounds (273587071301 / 1000000000000) (136793536729 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(673 / 800)
  have hx73 : Bounds (1473 / 800) (1473 / 800) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((673 / 800) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(673 / 800)
  have hx74 : Bounds (1473 / 800) (1473 / 800) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((673 / 800) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (38152793 / 62500000) (610444689 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (56199064089 / 50000000000) (561990641811 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(673 / 800)
  have hx77 : Bounds (-673 / 800) (-673 / 800) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((673 / 800) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (127 / 800) (127 / 800) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(673 / 800)
  have hx79 : Bounds (127 / 800) (127 / 800) x79 := by
    exact hx78
  let x80 : ℝ := -(673 / 800)
  have hx80 : Bounds (-673 / 800) (-673 / 800) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((673 / 800) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (127 / 800) (127 / 800) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(673 / 800)
  have hx82 : Bounds (127 / 800) (127 / 800) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1840424643 / 1000000000) (-5751327 / 3125000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-292167412077 / 1000000000000) (-730418529 / 2500000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (831813869703 / 1000000000000) (415906936011 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (415906934851 / 1000000000000) (415906936011 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (415906934851 / 1000000000000) (415906936011 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-415906936011 / 1000000000000) (-415906934851 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (277240243989 / 1000000000000) (277240246149 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (277240243989 / 1000000000000) (277240246149 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (673 / 800)
  have hx92 : Bounds (277240243989 / 1000000000000) (277240246149 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (273587071301 / 1000000000000) (277240246149 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (2735870713 / 20000000000) (5544804923 / 40000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (2735870713 / 20000000000) (5544804923 / 40000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(234439 / 250000)
  have hx98 : Bounds (484439 / 250000) (484439 / 250000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234439 / 250000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(234439 / 250000)
  have hx99 : Bounds (484439 / 250000) (484439 / 250000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234439 / 250000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (330765301 / 500000000) (661530603 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1281884893209 / 1000000000000) (1281884895147 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(234439 / 250000)
  have hx102 : Bounds (-234439 / 250000) (-234439 / 250000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234439 / 250000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (15561 / 250000) (15561 / 250000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(234439 / 250000)
  have hx104 : Bounds (15561 / 250000) (15561 / 250000) x104 := by
    exact hx103
  let x105 : ℝ := -(234439 / 250000)
  have hx105 : Bounds (-234439 / 250000) (-234439 / 250000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234439 / 250000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (15561 / 250000) (15561 / 250000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(234439 / 250000)
  have hx107 : Bounds (15561 / 250000) (15561 / 250000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-173543321 / 62500000) (-2776693131 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-86416243779 / 500000000000) (-34566497449 / 200000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1109052405651 / 1000000000000) (554526203951 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (22181048113 / 40000000000) (554526203951 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (22181048113 / 40000000000) (554526203951 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-554526203951 / 1000000000000) (-22181048113 / 40000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (138620976049 / 1000000000000) (5544839127 / 40000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (138620976049 / 1000000000000) (5544839127 / 40000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (234439 / 250000)
  have hx117 : Bounds (138620976049 / 1000000000000) (5544839127 / 40000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(938817 / 1000000)
  have hx119 : Bounds (1938817 / 1000000) (1938817 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((938817 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(938817 / 1000000)
  have hx120 : Bounds (1938817 / 1000000) (1938817 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((938817 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (662077993 / 1000000000) (331038997 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (641824034077 / 500000000000) (641824035047 / 500000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(938817 / 1000000)
  have hx123 : Bounds (-938817 / 1000000) (-938817 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((938817 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (61183 / 1000000) (61183 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(938817 / 1000000)
  have hx125 : Bounds (61183 / 1000000) (61183 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(938817 / 1000000)
  have hx126 : Bounds (-938817 / 1000000) (-938817 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((938817 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (61183 / 1000000) (61183 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(938817 / 1000000)
  have hx128 : Bounds (61183 / 1000000) (61183 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-698471477 / 250000000) (-2793885903 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-17093832151 / 100000000000) (-170938321203 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (278177436661 / 250000000000) (1112709748891 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (278177436661 / 500000000000) (278177437223 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (278177436661 / 500000000000) (278177437223 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-278177437223 / 500000000000) (-278177436661 / 500000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (68396152777 / 500000000000) (68396153839 / 500000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (68396152777 / 500000000000) (68396153839 / 500000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (938817 / 1000000)
  have hx138 : Bounds (68396152777 / 500000000000) (68396153839 / 500000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (234439 / 250000) (938817 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (938817 / 1000000) ≤ (68396153839 / 500000000000) := hx138.2
      have h2 : (2735870713 / 20000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (5544804923 / 40000000000) := hx96.2
      have h2 : (138620976049 / 1000000000000) ≤ biasE (234439 / 250000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1084470049987 / 1000000000000) (543109300747 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (37087123111 / 250000000000) (75285878113 / 500000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (37087123111 / 250000000000) (75285878113 / 500000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(234093 / 250000)
  have hx143 : Bounds (484093 / 250000) (484093 / 250000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234093 / 250000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(234093 / 250000)
  have hx144 : Bounds (484093 / 250000) (484093 / 250000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234093 / 250000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (660816119 / 1000000000) (16520403 / 25000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (63979291499 / 50000000000) (1279585831917 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(234093 / 250000)
  have hx147 : Bounds (-234093 / 250000) (-234093 / 250000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234093 / 250000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (15907 / 250000) (15907 / 250000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(234093 / 250000)
  have hx149 : Bounds (15907 / 250000) (15907 / 250000) x149 := by
    exact hx148
  let x150 : ℝ := -(234093 / 250000)
  have hx150 : Bounds (-234093 / 250000) (-234093 / 250000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234093 / 250000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (15907 / 250000) (15907 / 250000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(234093 / 250000)
  have hx152 : Bounds (15907 / 250000) (15907 / 250000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-344337707 / 125000000) (-688675413 / 250000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-21909519621 / 125000000000) (-175276156713 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (276077418253 / 250000000000) (276077418801 / 250000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (276077418253 / 500000000000) (276077418801 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (276077418253 / 500000000000) (276077418801 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-276077418801 / 500000000000) (-276077418253 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (70496171199 / 500000000000) (70496172247 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (70496171199 / 500000000000) (70496172247 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (234093 / 250000)
  have hx162 : Bounds (70496171199 / 500000000000) (70496172247 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(234373 / 250000)
  have hx164 : Bounds (484373 / 250000) (484373 / 250000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234373 / 250000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(234373 / 250000)
  have hx165 : Bounds (484373 / 250000) (484373 / 250000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234373 / 250000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (661394353 / 1000000000) (330697177 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (640723133891 / 500000000000) (1281446269721 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(234373 / 250000)
  have hx168 : Bounds (-234373 / 250000) (-234373 / 250000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234373 / 250000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (15627 / 250000) (15627 / 250000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(234373 / 250000)
  have hx170 : Bounds (15627 / 250000) (15627 / 250000) x170 := by
    exact hx169
  let x171 : ℝ := -(234373 / 250000)
  have hx171 : Bounds (-234373 / 250000) (-234373 / 250000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234373 / 250000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (15627 / 250000) (15627 / 250000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(234373 / 250000)
  have hx173 : Bounds (15627 / 250000) (15627 / 250000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-693115183 / 250000000) (-346557591 / 125000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-43325243859 / 250000000000) (-34660195037 / 200000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (554072646173 / 500000000000) (138518161817 / 125000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (554072646173 / 1000000000000) (138518161817 / 250000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (554072646173 / 1000000000000) (138518161817 / 250000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-138518161817 / 250000000000) (-554072646173 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (34768633183 / 250000000000) (139074534827 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (34768633183 / 250000000000) (139074534827 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (234373 / 250000)
  have hx183 : Bounds (34768633183 / 250000000000) (139074534827 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(234093 / 250000)
  have hx184 : Bounds (69454687283 / 500000000000) (140991176521 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((234093 / 250000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(234373 / 250000)
  have hx185 : Bounds (69537762439 / 500000000000) (17644977111 / 125000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((234373 / 250000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * (H (2*m)/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * (H (2*m)/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx96.1])
  have hcEq : biasE c = x141 * c := by
    have he := Reflection.regularContact_equation (x3 / x96)
    have hcdef : c = Reflection.regularContact (x3 / x96) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x96 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x96 := by linarith [hx96.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (234093 / 250000) (234373 / 250000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (234093 / 250000) ≤ (140991176521 / 1000000000000) := hx184.2
      have h2 : (70496171199 / 500000000000) ≤ biasE (234093 / 250000) := hx162.1
      linarith
    · have h1 : biasE (234373 / 250000) ≤ (139074534827 / 1000000000000) := hx183.2
      have h2 : (69537762439 / 500000000000) ≤ x141 * (234373 / 250000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (484439 / 250000) (1938817 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-938817 / 1000000) (-234439 / 250000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (61183 / 1000000) (15561 / 250000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (61183 / 1000000) (15561 / 250000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (16065805539489 / 1000000000000) (16344409394767 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (15565805539489 / 500000000000) (15844409394767 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (15565805539489 / 500000000000) (15844409394767 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1719111867 / 500000000) (3455963901 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1719111867 / 1000000000) (3455963901 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1719111867 / 1000000000) (3455963901 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (484093 / 250000) (484373 / 250000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-234373 / 250000) (-234093 / 250000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (15627 / 250000) (15907 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (15627 / 250000) (15907 / 250000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (3929087822971 / 250000000000) (15997952262111 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (3804087822971 / 125000000000) (15497952262111 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (3804087822971 / 125000000000) (15497952262111 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (341551777 / 100000000) (1716927543 / 500000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (341551777 / 200000000) (1716927543 / 1000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (341551777 / 200000000) (1716927543 / 1000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (164577685691 / 500000000000) (41737433139 / 125000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (2735870713 / 10000000000) (5544804923 / 20000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-5544804923 / 20000000000) (-2735870713 / 10000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (3244695327 / 62500000000) (15078098453 / 250000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (3244695327 / 62500000000) (15078098453 / 250000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (32242149359 / 20000000000) (1622258830823 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1622258830823 / 1000000000000) (-32242149359 / 20000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-1570343705591 / 1000000000000) (-775897537069 / 500000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-1570343705591 / 1000000000000) (-775897537069 / 500000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1572205523503 / 1000000000000) (1583194983597 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (232727239 / 125000000000) (31399909459 / 1000000000000) x218 := by
    apply bounds_add hx216 hx217 <;> norm_num
  have hpos : 0 < x218 := lt_of_lt_of_le (by norm_num) hx218.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x96)
        - (1 - 2*entropyInverse (H (2*m)/2)) *
            SmallMean.A (1 - 2*entropyInverse (H (2*m)/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*(H (2*m)/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (997 / 25600) (127 / 3200) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (997 / 25600) ≤ m → m ≤ (127 / 3200) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (127 / 3200) (207 / 5120) m) :
    let h := H (2*m)/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (1-4*m) = Real.log 2 * H (2*m) := by
    rw [show 1-4*m = 1-2*(2*m) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hm.1]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * (H (2*m)/2) = biasE (1-4*m)/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (127 / 1600) (207 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-207 / 2560) (-127 / 1600) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2353 / 2560) (1473 / 1600) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2353 / 2560) (1473 / 1600) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (127 / 800) (207 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-207 / 1280) (-127 / 800) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1073 / 1280) (673 / 800) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (1073 / 1280) (673 / 800) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1473 / 1600)
  have hx9 : Bounds (3073 / 1600) (3073 / 1600) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1473 / 1600) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1473 / 1600)
  have hx10 : Bounds (3073 / 1600) (3073 / 1600) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1473 / 1600) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (652650653 / 1000000000) (326325327 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (626748580209 / 500000000000) (1253497162339 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1473 / 1600)
  have hx13 : Bounds (-1473 / 1600) (-1473 / 1600) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1473 / 1600) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (127 / 1600) (127 / 1600) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1473 / 1600)
  have hx15 : Bounds (127 / 1600) (127 / 1600) x15 := by
    exact hx14
  let x16 : ℝ := -(1473 / 1600)
  have hx16 : Bounds (-1473 / 1600) (-1473 / 1600) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1473 / 1600) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (127 / 1600) (127 / 1600) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1473 / 1600)
  have hx18 : Bounds (127 / 1600) (127 / 1600) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-158348239 / 62500000) (-126678591 / 50000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-20110226353 / 100000000000) (-50275565803 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (131549362111 / 125000000000) (1052394899127 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (131549362111 / 250000000000) (131549362391 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (131549362111 / 250000000000) (131549362391 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-131549362391 / 250000000000) (-131549362111 / 250000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (41737432609 / 250000000000) (41737433139 / 250000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (41737432609 / 250000000000) (41737433139 / 250000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1473 / 1600)
  have hx28 : Bounds (41737432609 / 250000000000) (41737433139 / 250000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2353 / 2560)
  have hx30 : Bounds (4913 / 2560) (4913 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2353 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2353 / 2560)
  have hx31 : Bounds (4913 / 2560) (4913 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2353 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (325938747 / 500000000) (130375499 / 200000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (625522290629 / 500000000000) (625522291589 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2353 / 2560)
  have hx34 : Bounds (-2353 / 2560) (-2353 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2353 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (207 / 2560) (207 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2353 / 2560)
  have hx36 : Bounds (207 / 2560) (207 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(2353 / 2560)
  have hx37 : Bounds (-2353 / 2560) (-2353 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2353 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (207 / 2560) (207 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2353 / 2560)
  have hx39 : Bounds (207 / 2560) (207 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1257521873 / 500000000) (-1257521871 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-1016824327 / 5000000000) (-8134594603 / 40000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (523839857929 / 500000000000) (1047679718103 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (523839857929 / 1000000000000) (130959964763 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (523839857929 / 1000000000000) (130959964763 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-130959964763 / 250000000000) (-523839857929 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (42326830237 / 250000000000) (169307323071 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (42326830237 / 250000000000) (169307323071 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2353 / 2560)
  have hx49 : Bounds (42326830237 / 250000000000) (169307323071 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (41737432609 / 250000000000) (169307323071 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(673 / 800)
  have hx52 : Bounds (1473 / 800) (1473 / 800) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((673 / 800) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(673 / 800)
  have hx53 : Bounds (1473 / 800) (1473 / 800) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((673 / 800) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (38152793 / 62500000) (610444689 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (56199064089 / 50000000000) (561990641811 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(673 / 800)
  have hx56 : Bounds (-673 / 800) (-673 / 800) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((673 / 800) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (127 / 800) (127 / 800) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(673 / 800)
  have hx58 : Bounds (127 / 800) (127 / 800) x58 := by
    exact hx57
  let x59 : ℝ := -(673 / 800)
  have hx59 : Bounds (-673 / 800) (-673 / 800) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((673 / 800) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (127 / 800) (127 / 800) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(673 / 800)
  have hx61 : Bounds (127 / 800) (127 / 800) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1840424643 / 1000000000) (-5751327 / 3125000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-292167412077 / 1000000000000) (-730418529 / 2500000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (831813869703 / 1000000000000) (415906936011 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (415906934851 / 1000000000000) (415906936011 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (415906934851 / 1000000000000) (415906936011 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-415906936011 / 1000000000000) (-415906934851 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (277240243989 / 1000000000000) (277240246149 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (277240243989 / 1000000000000) (277240246149 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (673 / 800)
  have hx71 : Bounds (277240243989 / 1000000000000) (277240246149 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1073 / 1280)
  have hx73 : Bounds (2353 / 1280) (2353 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1073 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1073 / 1280)
  have hx74 : Bounds (2353 / 1280) (2353 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1073 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (608831031 / 1000000000) (76103879 / 125000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (223840533741 / 200000000000) (69950166909 / 62500000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1073 / 1280)
  have hx77 : Bounds (-1073 / 1280) (-1073 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1073 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (207 / 1280) (207 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1073 / 1280)
  have hx79 : Bounds (207 / 1280) (207 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(1073 / 1280)
  have hx80 : Bounds (-1073 / 1280) (-1073 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1073 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (207 / 1280) (207 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1073 / 1280)
  have hx82 : Bounds (207 / 1280) (207 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-147317417561 / 500000000000) (-58926966927 / 200000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (824567833583 / 1000000000000) (824567835909 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (412283916791 / 1000000000000) (82456783591 / 200000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (412283916791 / 1000000000000) (82456783591 / 200000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-82456783591 / 200000000000) (-412283916791 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (56172652409 / 200000000000) (280863264209 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (56172652409 / 200000000000) (280863264209 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1073 / 1280)
  have hx92 : Bounds (56172652409 / 200000000000) (280863264209 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (277240243989 / 1000000000000) (280863264209 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (69310060997 / 500000000000) (28086326421 / 200000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (69310060997 / 500000000000) (28086326421 / 200000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(9367 / 10000)
  have hx98 : Bounds (19367 / 10000) (19367 / 10000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9367 / 10000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(9367 / 10000)
  have hx99 : Bounds (19367 / 10000) (19367 / 10000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9367 / 10000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (660985493 / 1000000000) (330492747 / 500000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1280130604293 / 1000000000000) (128013060623 / 100000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(9367 / 10000)
  have hx102 : Bounds (-9367 / 10000) (-9367 / 10000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9367 / 10000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (633 / 10000) (633 / 10000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(9367 / 10000)
  have hx104 : Bounds (633 / 10000) (633 / 10000) x104 := by
    exact hx103
  let x105 : ℝ := -(9367 / 10000)
  have hx105 : Bounds (-9367 / 10000) (-9367 / 10000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9367 / 10000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (633 / 10000) (633 / 10000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(9367 / 10000)
  have hx107 : Bounds (633 / 10000) (633 / 10000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-5390371 / 1953125) (-689967487 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-87349883981 / 500000000000) (-43674941927 / 250000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1105430836331 / 1000000000000) (552715419261 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (110543083633 / 200000000000) (552715419261 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (110543083633 / 200000000000) (552715419261 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-552715419261 / 1000000000000) (-110543083633 / 200000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (140431760739 / 1000000000000) (28086352567 / 200000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (140431760739 / 1000000000000) (28086352567 / 200000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (9367 / 10000)
  have hx117 : Bounds (140431760739 / 1000000000000) (28086352567 / 200000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(937757 / 1000000)
  have hx119 : Bounds (1937757 / 1000000) (1937757 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((937757 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(937757 / 1000000)
  have hx120 : Bounds (1937757 / 1000000) (1937757 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((937757 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (330765559 / 500000000) (661531119 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (640943277311 / 500000000000) (1281886556561 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(937757 / 1000000)
  have hx123 : Bounds (-937757 / 1000000) (-937757 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((937757 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (62243 / 1000000) (62243 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(937757 / 1000000)
  have hx125 : Bounds (62243 / 1000000) (62243 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(937757 / 1000000)
  have hx126 : Bounds (-937757 / 1000000) (-937757 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((937757 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (62243 / 1000000) (62243 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(937757 / 1000000)
  have hx128 : Bounds (62243 / 1000000) (62243 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1388354601 / 500000000) (-2776709197 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-172830710861 / 1000000000000) (-43207677637 / 250000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1109055843761 / 1000000000000) (1109055846013 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (13863198047 / 25000000000) (554527923007 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (13863198047 / 25000000000) (554527923007 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-554527923007 / 1000000000000) (-13863198047 / 25000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (138619256993 / 1000000000000) (1732740739 / 12500000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (138619256993 / 1000000000000) (1732740739 / 12500000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (937757 / 1000000)
  have hx138 : Bounds (138619256993 / 1000000000000) (1732740739 / 12500000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (9367 / 10000) (937757 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (937757 / 1000000) ≤ (1732740739 / 12500000000) := hx138.2
      have h2 : (69310060997 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (28086326421 / 200000000000) := hx96.2
      have h2 : (140431760739 / 1000000000000) ≤ biasE (9367 / 10000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1086218601493 / 1000000000000) (27199320017 / 25000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (150571755051 / 1000000000000) (76392898043 / 500000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (150571755051 / 1000000000000) (76392898043 / 500000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(187051 / 200000)
  have hx143 : Bounds (387051 / 200000) (387051 / 200000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((187051 / 200000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(187051 / 200000)
  have hx144 : Bounds (387051 / 200000) (387051 / 200000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((187051 / 200000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (6602391 / 10000000) (660239101 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (127773101947 / 100000000000) (638865510703 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(187051 / 200000)
  have hx147 : Bounds (-187051 / 200000) (-187051 / 200000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((187051 / 200000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (12949 / 200000) (12949 / 200000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(187051 / 200000)
  have hx149 : Bounds (12949 / 200000) (12949 / 200000) x149 := by
    exact hx148
  let x150 : ℝ := -(187051 / 200000)
  have hx150 : Bounds (-187051 / 200000) (-187051 / 200000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((187051 / 200000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (12949 / 200000) (12949 / 200000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(187051 / 200000)
  have hx152 : Bounds (12949 / 200000) (12949 / 200000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-2737298803 / 1000000000) (-2737298799 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-177226411001 / 1000000000000) (-177226410741 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1100504608469 / 1000000000000) (220100922133 / 200000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (275126152117 / 500000000000) (550252305333 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (275126152117 / 500000000000) (550252305333 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-550252305333 / 1000000000000) (-275126152117 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (142894874667 / 1000000000000) (71447438383 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (142894874667 / 1000000000000) (71447438383 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (187051 / 200000)
  have hx162 : Bounds (142894874667 / 1000000000000) (71447438383 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(936373 / 1000000)
  have hx164 : Bounds (1936373 / 1000000) (1936373 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((936373 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(936373 / 1000000)
  have hx165 : Bounds (1936373 / 1000000) (1936373 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((936373 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (132163327 / 200000000) (165204159 / 250000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (319896872491 / 250000000000) (639793745951 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(936373 / 1000000)
  have hx168 : Bounds (-936373 / 1000000) (-936373 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((936373 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (63627 / 1000000) (63627 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(936373 / 1000000)
  have hx170 : Bounds (63627 / 1000000) (63627 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(936373 / 1000000)
  have hx171 : Bounds (-936373 / 1000000) (-936373 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((936373 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (63627 / 1000000) (63627 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(936373 / 1000000)
  have hx173 : Bounds (63627 / 1000000) (63627 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-688679343 / 250000000) (-344339671 / 125000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-175274402229 / 1000000000000) (-175274401973 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (220862617547 / 200000000000) (1104313089929 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (552156543867 / 1000000000000) (110431308993 / 200000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (552156543867 / 1000000000000) (110431308993 / 200000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-110431308993 / 200000000000) (-552156543867 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (28198127007 / 200000000000) (140990637133 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (28198127007 / 200000000000) (140990637133 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (936373 / 1000000)
  have hx183 : Bounds (28198127007 / 200000000000) (140990637133 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(187051 / 200000)
  have hx184 : Bounds (14082298677 / 100000000000) (142893679719 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((187051 / 200000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(936373 / 1000000)
  have hx185 : Bounds (17623915749 / 125000000000) (143064494239 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((936373 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * (H (2*m)/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * (H (2*m)/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx96.1])
  have hcEq : biasE c = x141 * c := by
    have he := Reflection.regularContact_equation (x3 / x96)
    have hcdef : c = Reflection.regularContact (x3 / x96) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x96 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x96 := by linarith [hx96.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (187051 / 200000) (936373 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (187051 / 200000) ≤ (142893679719 / 1000000000000) := hx184.2
      have h2 : (142894874667 / 1000000000000) ≤ biasE (187051 / 200000) := hx162.1
      linarith
    · have h1 : biasE (936373 / 1000000) ≤ (140990637133 / 1000000000000) := hx183.2
      have h2 : (17623915749 / 125000000000) ≤ x141 * (936373 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (19367 / 10000) (1937757 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-937757 / 1000000) (-9367 / 10000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (62243 / 1000000) (633 / 10000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (62243 / 1000000) (633 / 10000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (3949447077409 / 250000000000) (3213212730749 / 200000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (3824447077409 / 125000000000) (3113212730749 / 100000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (3824447077409 / 125000000000) (3113212730749 / 100000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (3420855441 / 1000000000) (3438240321 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (3420855441 / 2000000000) (3438240321 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (3420855441 / 2000000000) (3438240321 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (387051 / 200000) (1936373 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-936373 / 1000000) (-187051 / 200000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (63627 / 1000000) (12949 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (63627 / 1000000) (12949 / 200000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (15445208124179 / 1000000000000) (3143319659893 / 200000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (14945208124179 / 500000000000) (3043319659893 / 100000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (14945208124179 / 500000000000) (3043319659893 / 100000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (3397537899 / 1000000000) (426941751 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (3397537899 / 2000000000) (426941751 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (3397537899 / 2000000000) (426941751 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (41737432609 / 125000000000) (169307323071 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (69310060997 / 250000000000) (28086326421 / 100000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-28086326421 / 100000000000) (-69310060997 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (26518098331 / 500000000000) (30687201077 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (26518098331 / 500000000000) (30687201077 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (50067426431 / 31250000000) (32242339287 / 20000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-32242339287 / 20000000000) (-50067426431 / 31250000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-194885095961 / 125000000000) (-770391621819 / 500000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-194885095961 / 125000000000) (-770391621819 / 500000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (780703776987 / 500000000000) (786106499029 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1163393143 / 500000000000) (1571487721 / 50000000000) x218 := by
    apply bounds_add hx216 hx217 <;> norm_num
  have hpos : 0 < x218 := lt_of_lt_of_le (by norm_num) hx218.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x96)
        - (1 - 2*entropyInverse (H (2*m)/2)) *
            SmallMean.A (1 - 2*entropyInverse (H (2*m)/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*(H (2*m)/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (127 / 3200) (207 / 5120) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (127 / 3200) ≤ m → m ≤ (207 / 5120) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (207 / 5120) (527 / 12800) m) :
    let h := H (2*m)/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (1-4*m) = Real.log 2 * H (2*m) := by
    rw [show 1-4*m = 1-2*(2*m) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hm.1]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * (H (2*m)/2) = biasE (1-4*m)/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (207 / 2560) (527 / 6400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-527 / 6400) (-207 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (5873 / 6400) (2353 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (5873 / 6400) (2353 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (207 / 1280) (527 / 3200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-527 / 3200) (-207 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2673 / 3200) (1073 / 1280) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (2673 / 3200) (1073 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2353 / 2560)
  have hx9 : Bounds (4913 / 2560) (4913 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2353 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2353 / 2560)
  have hx10 : Bounds (4913 / 2560) (4913 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2353 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (325938747 / 500000000) (130375499 / 200000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (625522290629 / 500000000000) (625522291589 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2353 / 2560)
  have hx13 : Bounds (-2353 / 2560) (-2353 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2353 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (207 / 2560) (207 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2353 / 2560)
  have hx15 : Bounds (207 / 2560) (207 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(2353 / 2560)
  have hx16 : Bounds (-2353 / 2560) (-2353 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2353 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (207 / 2560) (207 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2353 / 2560)
  have hx18 : Bounds (207 / 2560) (207 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1257521873 / 500000000) (-1257521871 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-1016824327 / 5000000000) (-8134594603 / 40000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (523839857929 / 500000000000) (1047679718103 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (523839857929 / 1000000000000) (130959964763 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (523839857929 / 1000000000000) (130959964763 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-130959964763 / 250000000000) (-523839857929 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (42326830237 / 250000000000) (169307323071 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (42326830237 / 250000000000) (169307323071 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2353 / 2560)
  have hx28 : Bounds (42326830237 / 250000000000) (169307323071 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(5873 / 6400)
  have hx30 : Bounds (12273 / 6400) (12273 / 6400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5873 / 6400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(5873 / 6400)
  have hx31 : Bounds (12273 / 6400) (12273 / 6400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5873 / 6400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (651103737 / 1000000000) (325551869 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (19509267979 / 15625000000) (49943726103 / 40000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(5873 / 6400)
  have hx34 : Bounds (-5873 / 6400) (-5873 / 6400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5873 / 6400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (527 / 6400) (527 / 6400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(5873 / 6400)
  have hx36 : Bounds (527 / 6400) (527 / 6400) x36 := by
    exact hx35
  let x37 : ℝ := -(5873 / 6400)
  have hx37 : Bounds (-5873 / 6400) (-5873 / 6400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5873 / 6400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (527 / 6400) (527 / 6400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(5873 / 6400)
  have hx39 : Bounds (527 / 6400) (527 / 6400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-2496852723 / 1000000000) (-2496852719 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-20560021641 / 100000000000) (-2570002701 / 12500000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (521496467123 / 500000000000) (208598587299 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (521496467123 / 1000000000000) (65187058531 / 125000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (521496467123 / 1000000000000) (65187058531 / 125000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-65187058531 / 125000000000) (-521496467123 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (21456338969 / 125000000000) (171650713877 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (21456338969 / 125000000000) (171650713877 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (5873 / 6400)
  have hx49 : Bounds (21456338969 / 125000000000) (171650713877 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (42326830237 / 250000000000) (171650713877 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1073 / 1280)
  have hx52 : Bounds (2353 / 1280) (2353 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1073 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1073 / 1280)
  have hx53 : Bounds (2353 / 1280) (2353 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1073 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (608831031 / 1000000000) (76103879 / 125000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (223840533741 / 200000000000) (69950166909 / 62500000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1073 / 1280)
  have hx56 : Bounds (-1073 / 1280) (-1073 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1073 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (207 / 1280) (207 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1073 / 1280)
  have hx58 : Bounds (207 / 1280) (207 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(1073 / 1280)
  have hx59 : Bounds (-1073 / 1280) (-1073 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1073 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (207 / 1280) (207 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1073 / 1280)
  have hx61 : Bounds (207 / 1280) (207 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-147317417561 / 500000000000) (-58926966927 / 200000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (824567833583 / 1000000000000) (824567835909 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (412283916791 / 1000000000000) (82456783591 / 200000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (412283916791 / 1000000000000) (82456783591 / 200000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-82456783591 / 200000000000) (-412283916791 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (56172652409 / 200000000000) (280863264209 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (56172652409 / 200000000000) (280863264209 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1073 / 1280)
  have hx71 : Bounds (56172652409 / 200000000000) (280863264209 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2673 / 3200)
  have hx73 : Bounds (5873 / 3200) (5873 / 3200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2673 / 3200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2673 / 3200)
  have hx74 : Bounds (5873 / 3200) (5873 / 3200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2673 / 3200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (303607383 / 500000000) (607214767 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (69651803139 / 62500000000) (55721442603 / 50000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2673 / 3200)
  have hx77 : Bounds (-2673 / 3200) (-2673 / 3200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2673 / 3200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (527 / 3200) (527 / 3200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2673 / 3200)
  have hx79 : Bounds (527 / 3200) (527 / 3200) x79 := by
    exact hx78
  let x80 : ℝ := -(2673 / 3200)
  have hx80 : Bounds (-2673 / 3200) (-2673 / 3200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2673 / 3200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (527 / 3200) (527 / 3200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2673 / 3200)
  have hx82 : Bounds (527 / 3200) (527 / 3200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-901852771 / 500000000) (-1803705539 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-297047756449 / 1000000000000) (-148523877977 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (32695243751 / 40000000000) (408690548053 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (408690546887 / 1000000000000) (408690548053 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (408690546887 / 1000000000000) (408690548053 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-408690548053 / 1000000000000) (-408690546887 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (284456631947 / 1000000000000) (284456634113 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (284456631947 / 1000000000000) (284456634113 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2673 / 3200)
  have hx92 : Bounds (284456631947 / 1000000000000) (284456634113 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (56172652409 / 200000000000) (284456634113 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (70215815511 / 500000000000) (142228317057 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (70215815511 / 500000000000) (142228317057 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(935647 / 1000000)
  have hx98 : Bounds (1935647 / 1000000) (1935647 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((935647 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(935647 / 1000000)
  have hx99 : Bounds (1935647 / 1000000) (1935647 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((935647 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (660441637 / 1000000000) (330220819 / 500000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (639190936667 / 500000000000) (127838187527 / 100000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(935647 / 1000000)
  have hx102 : Bounds (-935647 / 1000000) (-935647 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((935647 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (64353 / 1000000) (64353 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(935647 / 1000000)
  have hx104 : Bounds (64353 / 1000000) (64353 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(935647 / 1000000)
  have hx105 : Bounds (-935647 / 1000000) (-935647 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((935647 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (64353 / 1000000) (64353 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(935647 / 1000000)
  have hx107 : Bounds (64353 / 1000000) (64353 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-171460733 / 62500000) (-685842931 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-44136050203 / 250000000000) (-88272100277 / 500000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (550918836261 / 500000000000) (275459418679 / 250000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (550918836261 / 1000000000000) (275459418679 / 500000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (550918836261 / 1000000000000) (275459418679 / 500000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-275459418679 / 500000000000) (-550918836261 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (71114171321 / 500000000000) (142228344739 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (71114171321 / 500000000000) (142228344739 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (935647 / 1000000)
  have hx117 : Bounds (71114171321 / 500000000000) (142228344739 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(936701 / 1000000)
  have hx119 : Bounds (1936701 / 1000000) (1936701 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((936701 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(936701 / 1000000)
  have hx120 : Bounds (1936701 / 1000000) (1936701 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((936701 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (66098601 / 100000000) (660986011 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1280132266553 / 1000000000000) (128013226849 / 100000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(936701 / 1000000)
  have hx123 : Bounds (-936701 / 1000000) (-936701 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((936701 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (63299 / 1000000) (63299 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(936701 / 1000000)
  have hx125 : Bounds (63299 / 1000000) (63299 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(936701 / 1000000)
  have hx126 : Bounds (-936701 / 1000000) (-936701 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((936701 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (63299 / 1000000) (63299 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(936701 / 1000000)
  have hx128 : Bounds (63299 / 1000000) (63299 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-11039543 / 4000000) (-1379942873 / 500000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-17469800809 / 100000000000) (-43674501959 / 250000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1105434258463 / 1000000000000) (552717130327 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (552717129231 / 1000000000000) (552717130327 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (552717129231 / 1000000000000) (552717130327 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-552717130327 / 1000000000000) (-552717129231 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (140430049673 / 1000000000000) (140430051769 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (140430049673 / 1000000000000) (140430051769 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (936701 / 1000000)
  have hx138 : Bounds (140430049673 / 1000000000000) (140430051769 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (935647 / 1000000) (936701 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (936701 / 1000000) ≤ (140430051769 / 1000000000000) := hx138.2
      have h2 : (70215815511 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (142228317057 / 1000000000000) := hx96.2
      have h2 : (71114171321 / 500000000000) ≤ biasE (935647 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1087972800679 / 1000000000000) (544866337477 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (76392897453 / 500000000000) (154990844401 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (76392897453 / 500000000000) (154990844401 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(46707 / 50000)
  have hx143 : Bounds (96707 / 50000) (96707 / 50000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46707 / 50000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(46707 / 50000)
  have hx144 : Bounds (96707 / 50000) (96707 / 50000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46707 / 50000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (659662783 / 1000000000) (10307231 / 15625000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1275880175111 / 1000000000000) (637940088523 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(46707 / 50000)
  have hx147 : Bounds (-46707 / 50000) (-46707 / 50000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46707 / 50000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (3293 / 50000) (3293 / 50000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(46707 / 50000)
  have hx149 : Bounds (3293 / 50000) (3293 / 50000) x149 := by
    exact hx148
  let x150 : ℝ := -(46707 / 50000)
  have hx150 : Bounds (-46707 / 50000) (-46707 / 50000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46707 / 50000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (3293 / 50000) (3293 / 50000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(46707 / 50000)
  have hx152 : Bounds (3293 / 50000) (3293 / 50000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-680056001 / 250000000) (-85007 / 31250) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-22394244113 / 125000000000) (-279928051 / 1562500000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1096726222207 / 1000000000000) (548363112203 / 500000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (548363111103 / 1000000000000) (548363112203 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (548363111103 / 1000000000000) (548363112203 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-548363112203 / 1000000000000) (-548363111103 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (144784067797 / 1000000000000) (144784069897 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (144784067797 / 1000000000000) (144784069897 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (46707 / 50000)
  have hx162 : Bounds (144784067797 / 1000000000000) (144784069897 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(116907 / 125000)
  have hx164 : Bounds (241907 / 125000) (241907 / 125000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((116907 / 125000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(116907 / 125000)
  have hx165 : Bounds (241907 / 125000) (241907 / 125000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((116907 / 125000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (660239617 / 1000000000) (330119809 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (319433170059 / 250000000000) (1277732682173 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(116907 / 125000)
  have hx168 : Bounds (-116907 / 125000) (-116907 / 125000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((116907 / 125000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (8093 / 125000) (8093 / 125000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(116907 / 125000)
  have hx170 : Bounds (8093 / 125000) (8093 / 125000) x170 := by
    exact hx169
  let x171 : ℝ := -(116907 / 125000)
  have hx171 : Bounds (-116907 / 125000) (-116907 / 125000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((116907 / 125000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (8093 / 125000) (8093 / 125000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(116907 / 125000)
  have hx173 : Bounds (8093 / 125000) (8093 / 125000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-2737314249 / 1000000000) (-547462849 / 200000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-88612336869 / 500000000000) (-88612336739 / 500000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (550254003249 / 500000000000) (220101601739 / 200000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (550254003249 / 1000000000000) (137563501087 / 250000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (550254003249 / 1000000000000) (137563501087 / 250000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-137563501087 / 250000000000) (-550254003249 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (35723293913 / 250000000000) (142893177751 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (35723293913 / 250000000000) (142893177751 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (116907 / 125000)
  have hx183 : Bounds (35723293913 / 250000000000) (142893177751 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(46707 / 50000)
  have hx184 : Bounds (142723322453 / 1000000000000) (144783147389 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((46707 / 50000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(116907 / 125000)
  have hx185 : Bounds (714469157 / 5000000000) (36239029293 / 250000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((116907 / 125000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * (H (2*m)/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * (H (2*m)/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx96.1])
  have hcEq : biasE c = x141 * c := by
    have he := Reflection.regularContact_equation (x3 / x96)
    have hcdef : c = Reflection.regularContact (x3 / x96) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x96 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x96 := by linarith [hx96.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (46707 / 50000) (116907 / 125000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (46707 / 50000) ≤ (144783147389 / 1000000000000) := hx184.2
      have h2 : (144784067797 / 1000000000000) ≤ biasE (46707 / 50000) := hx162.1
      linarith
    · have h1 : biasE (116907 / 125000) ≤ (142893177751 / 1000000000000) := hx183.2
      have h2 : (714469157 / 5000000000) ≤ x141 * (116907 / 125000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1935647 / 1000000) (1936701 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-936701 / 1000000) (-935647 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (63299 / 1000000) (64353 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (63299 / 1000000) (64353 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (776964554877 / 50000000000) (3159607576739 / 200000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (751964554877 / 25000000000) (3059607576739 / 100000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (751964554877 / 25000000000) (3059607576739 / 100000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (3403813361 / 1000000000) (42760897 / 12500000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (3403813361 / 2000000000) (42760897 / 25000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (3403813361 / 2000000000) (42760897 / 25000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (96707 / 50000) (241907 / 125000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-116907 / 125000) (-46707 / 50000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (8093 / 125000) (3293 / 50000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (8093 / 125000) (3293 / 50000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (15183723048891 / 1000000000000) (15445446682319 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (14683723048891 / 500000000000) (14945446682319 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (14683723048891 / 500000000000) (14945446682319 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (3379886783 / 1000000000) (3397553867 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (3379886783 / 2000000000) (3397553867 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (3379886783 / 2000000000) (3397553867 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (42326830237 / 125000000000) (171650713877 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (70215815511 / 250000000000) (142228317057 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-142228317057 / 500000000000) (-70215815511 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (27079003891 / 500000000000) (6243816571 / 100000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (27079003891 / 500000000000) (6243816571 / 100000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1592383879889 / 1000000000000) (25033859363 / 15625000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-25033859363 / 15625000000) (-1592383879889 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-30960179829 / 20000000000) (-1529945714179 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-30960179829 / 20000000000) (-1529945714179 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (387696778839 / 250000000000) (1561414892393 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1389061953 / 500000000000) (15734589107 / 500000000000) x218 := by
    apply bounds_add hx216 hx217 <;> norm_num
  have hpos : 0 < x218 := lt_of_lt_of_le (by norm_num) hx218.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x96)
        - (1 - 2*entropyInverse (H (2*m)/2)) *
            SmallMean.A (1 - 2*entropyInverse (H (2*m)/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*(H (2*m)/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (207 / 5120) (527 / 12800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (207 / 5120) ≤ m → m ≤ (527 / 12800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (527 / 12800) (1073 / 25600) m) :
    let h := H (2*m)/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (1-4*m) = Real.log 2 * H (2*m) := by
    rw [show 1-4*m = 1-2*(2*m) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hm.1]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * (H (2*m)/2) = biasE (1-4*m)/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (527 / 6400) (1073 / 12800) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1073 / 12800) (-527 / 6400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (11727 / 12800) (5873 / 6400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (11727 / 12800) (5873 / 6400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (527 / 3200) (1073 / 6400) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1073 / 6400) (-527 / 3200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (5327 / 6400) (2673 / 3200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (5327 / 6400) (2673 / 3200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(5873 / 6400)
  have hx9 : Bounds (12273 / 6400) (12273 / 6400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5873 / 6400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(5873 / 6400)
  have hx10 : Bounds (12273 / 6400) (12273 / 6400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5873 / 6400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (651103737 / 1000000000) (325551869 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (19509267979 / 15625000000) (49943726103 / 40000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(5873 / 6400)
  have hx13 : Bounds (-5873 / 6400) (-5873 / 6400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5873 / 6400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (527 / 6400) (527 / 6400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(5873 / 6400)
  have hx15 : Bounds (527 / 6400) (527 / 6400) x15 := by
    exact hx14
  let x16 : ℝ := -(5873 / 6400)
  have hx16 : Bounds (-5873 / 6400) (-5873 / 6400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5873 / 6400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (527 / 6400) (527 / 6400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(5873 / 6400)
  have hx18 : Bounds (527 / 6400) (527 / 6400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-2496852723 / 1000000000) (-2496852719 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-20560021641 / 100000000000) (-2570002701 / 12500000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (521496467123 / 500000000000) (208598587299 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (521496467123 / 1000000000000) (65187058531 / 125000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (521496467123 / 1000000000000) (65187058531 / 125000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-65187058531 / 125000000000) (-521496467123 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (21456338969 / 125000000000) (171650713877 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (21456338969 / 125000000000) (171650713877 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (5873 / 6400)
  have hx28 : Bounds (21456338969 / 125000000000) (171650713877 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(11727 / 12800)
  have hx30 : Bounds (24527 / 12800) (24527 / 12800) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11727 / 12800) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(11727 / 12800)
  have hx31 : Bounds (24527 / 12800) (24527 / 12800) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11727 / 12800) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (32516469 / 50000000) (650329381 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (623071433721 / 500000000000) (1246142869359 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(11727 / 12800)
  have hx34 : Bounds (-11727 / 12800) (-11727 / 12800) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11727 / 12800) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1073 / 12800) (1073 / 12800) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(11727 / 12800)
  have hx36 : Bounds (1073 / 12800) (1073 / 12800) x36 := by
    exact hx35
  let x37 : ℝ := -(11727 / 12800)
  have hx37 : Bounds (-11727 / 12800) (-11727 / 12800) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11727 / 12800) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1073 / 12800) (1073 / 12800) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(11727 / 12800)
  have hx39 : Bounds (1073 / 12800) (1073 / 12800) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-2478986709 / 1000000000) (-495797341 / 200000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-51952201929 / 250000000000) (-10390440369 / 50000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (519167029863 / 500000000000) (1038334061979 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (519167029863 / 1000000000000) (51916703099 / 100000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (519167029863 / 1000000000000) (51916703099 / 100000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-51916703099 / 100000000000) (-519167029863 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (17398014901 / 100000000000) (173980151137 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (17398014901 / 100000000000) (173980151137 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (11727 / 12800)
  have hx49 : Bounds (17398014901 / 100000000000) (173980151137 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (21456338969 / 125000000000) (173980151137 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2673 / 3200)
  have hx52 : Bounds (5873 / 3200) (5873 / 3200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2673 / 3200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2673 / 3200)
  have hx53 : Bounds (5873 / 3200) (5873 / 3200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2673 / 3200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (303607383 / 500000000) (607214767 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (69651803139 / 62500000000) (55721442603 / 50000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2673 / 3200)
  have hx56 : Bounds (-2673 / 3200) (-2673 / 3200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2673 / 3200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (527 / 3200) (527 / 3200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2673 / 3200)
  have hx58 : Bounds (527 / 3200) (527 / 3200) x58 := by
    exact hx57
  let x59 : ℝ := -(2673 / 3200)
  have hx59 : Bounds (-2673 / 3200) (-2673 / 3200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2673 / 3200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (527 / 3200) (527 / 3200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2673 / 3200)
  have hx61 : Bounds (527 / 3200) (527 / 3200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-901852771 / 500000000) (-1803705539 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-297047756449 / 1000000000000) (-148523877977 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (32695243751 / 40000000000) (408690548053 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (408690546887 / 1000000000000) (408690548053 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (408690546887 / 1000000000000) (408690548053 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-408690548053 / 1000000000000) (-408690546887 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (284456631947 / 1000000000000) (284456634113 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (284456631947 / 1000000000000) (284456634113 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2673 / 3200)
  have hx71 : Bounds (284456631947 / 1000000000000) (284456634113 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(5327 / 6400)
  have hx73 : Bounds (11727 / 6400) (11727 / 6400) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5327 / 6400) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(5327 / 6400)
  have hx74 : Bounds (11727 / 6400) (11727 / 6400) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5327 / 6400) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (121119177 / 200000000) (302797943 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (221931966981 / 200000000000) (554829918369 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(5327 / 6400)
  have hx77 : Bounds (-5327 / 6400) (-5327 / 6400) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5327 / 6400) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1073 / 6400) (1073 / 6400) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(5327 / 6400)
  have hx79 : Bounds (1073 / 6400) (1073 / 6400) x79 := by
    exact hx78
  let x80 : ℝ := -(5327 / 6400)
  have hx80 : Bounds (-5327 / 6400) (-5327 / 6400) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5327 / 6400) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1073 / 6400) (1073 / 6400) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(5327 / 6400)
  have hx82 : Bounds (1073 / 6400) (1073 / 6400) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-223229941 / 125000000) (-71433581 / 40000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-299407158367 / 1000000000000) (-299407157863 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (405126338269 / 500000000000) (6482021431 / 8000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (405126338269 / 1000000000000) (202563169719 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (405126338269 / 1000000000000) (202563169719 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-202563169719 / 500000000000) (-405126338269 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (144010420281 / 500000000000) (288020842731 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (144010420281 / 500000000000) (288020842731 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (5327 / 6400)
  have hx92 : Bounds (144010420281 / 500000000000) (288020842731 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (284456631947 / 1000000000000) (288020842731 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (142228315973 / 1000000000000) (72005210683 / 500000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (142228315973 / 1000000000000) (72005210683 / 500000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(934597 / 1000000)
  have hx98 : Bounds (1934597 / 1000000) (1934597 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((934597 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(934597 / 1000000)
  have hx99 : Bounds (1934597 / 1000000) (1934597 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((934597 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (164974759 / 250000000) (659899037 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (319159673837 / 250000000000) (319159674321 / 250000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(934597 / 1000000)
  have hx102 : Bounds (-934597 / 1000000) (-934597 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((934597 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (65403 / 1000000) (65403 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(934597 / 1000000)
  have hx104 : Bounds (65403 / 1000000) (65403 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(934597 / 1000000)
  have hx105 : Bounds (-934597 / 1000000) (-934597 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((934597 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (65403 / 1000000) (65403 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(934597 / 1000000)
  have hx107 : Bounds (65403 / 1000000) (65403 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-170449197 / 62500000) (-681796787 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-178366221303 / 1000000000000) (-2229577763 / 12500000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (219654494809 / 200000000000) (274568119061 / 250000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (274568118511 / 500000000000) (274568119061 / 500000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (274568118511 / 500000000000) (274568119061 / 500000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-274568119061 / 500000000000) (-274568118511 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (72005470939 / 500000000000) (72005471989 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (72005470939 / 500000000000) (72005471989 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (934597 / 1000000)
  have hx117 : Bounds (72005470939 / 500000000000) (72005471989 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(29239 / 31250)
  have hx119 : Bounds (60489 / 31250) (60489 / 31250) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((29239 / 31250) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(29239 / 31250)
  have hx120 : Bounds (60489 / 31250) (60489 / 31250) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((29239 / 31250) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (330221077 / 500000000) (132088431 / 200000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (255676706901 / 200000000000) (639191768221 / 500000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(29239 / 31250)
  have hx123 : Bounds (-29239 / 31250) (-29239 / 31250) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((29239 / 31250) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (2011 / 31250) (2011 / 31250) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(29239 / 31250)
  have hx125 : Bounds (2011 / 31250) (2011 / 31250) x125 := by
    exact hx124
  let x126 : ℝ := -(29239 / 31250)
  have hx126 : Bounds (-29239 / 31250) (-29239 / 31250) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((29239 / 31250) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (2011 / 31250) (2011 / 31250) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(29239 / 31250)
  have hx128 : Bounds (2011 / 31250) (2011 / 31250) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-2743387267 / 1000000000) (-2743387263 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-88271228703 / 500000000000) (-44135614287 / 250000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1101841077099 / 1000000000000) (550920539647 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (550920538549 / 1000000000000) (550920539647 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (550920538549 / 1000000000000) (550920539647 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-550920539647 / 1000000000000) (-550920538549 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (142226640353 / 1000000000000) (142226642451 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (142226640353 / 1000000000000) (142226642451 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (29239 / 31250)
  have hx138 : Bounds (142226640353 / 1000000000000) (142226642451 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (934597 / 1000000) (29239 / 31250) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (29239 / 31250) ≤ (142226642451 / 1000000000000) := hx138.2
      have h2 : (142228315973 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (72005210683 / 500000000000) := hx96.2
      have h2 : (72005470939 / 500000000000) ≤ biasE (934597 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1089732674953 / 1000000000000) (545749125949 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (154990843219 / 1000000000000) (157187123177 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (154990843219 / 1000000000000) (157187123177 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(933027 / 1000000)
  have hx143 : Bounds (1933027 / 1000000) (1933027 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((933027 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(933027 / 1000000)
  have hx144 : Bounds (1933027 / 1000000) (1933027 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((933027 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (10298237 / 15625000) (659087169 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1274033291097 / 1000000000000) (1274033293031 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(933027 / 1000000)
  have hx147 : Bounds (-933027 / 1000000) (-933027 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((933027 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (66973 / 1000000) (66973 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(933027 / 1000000)
  have hx149 : Bounds (66973 / 1000000) (66973 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(933027 / 1000000)
  have hx150 : Bounds (-933027 / 1000000) (-933027 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((933027 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (66973 / 1000000) (66973 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(933027 / 1000000)
  have hx152 : Bounds (66973 / 1000000) (66973 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-10560413 / 3906250) (-675866431 / 250000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-90529605101 / 500000000000) (-181059209933 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (218594816179 / 200000000000) (546487041549 / 500000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (546487040447 / 1000000000000) (546487041549 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (546487040447 / 1000000000000) (546487041549 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-546487041549 / 1000000000000) (-546487040447 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (146660138451 / 1000000000000) (146660140553 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (146660138451 / 1000000000000) (146660140553 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (933027 / 1000000)
  have hx162 : Bounds (146660138451 / 1000000000000) (146660140553 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(934141 / 1000000)
  have hx164 : Bounds (1934141 / 1000000) (1934141 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((934141 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(934141 / 1000000)
  have hx165 : Bounds (1934141 / 1000000) (1934141 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((934141 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (6596633 / 10000000) (659663301 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (51035273389 / 40000000000) (63794091833 / 50000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(934141 / 1000000)
  have hx168 : Bounds (-934141 / 1000000) (-934141 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((934141 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (65859 / 1000000) (65859 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(934141 / 1000000)
  have hx170 : Bounds (65859 / 1000000) (65859 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(934141 / 1000000)
  have hx171 : Bounds (-934141 / 1000000) (-934141 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((934141 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (65859 / 1000000) (65859 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(934141 / 1000000)
  have hx173 : Bounds (65859 / 1000000) (65859 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-680059797 / 250000000) (-170014949 / 62500000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-179152232683 / 1000000000000) (-179152232419 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (548364801021 / 500000000000) (1096729604241 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (548364801021 / 1000000000000) (548364802121 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (548364801021 / 1000000000000) (548364802121 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-548364802121 / 1000000000000) (-548364801021 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (144782377879 / 1000000000000) (144782379979 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (144782377879 / 1000000000000) (144782379979 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (934141 / 1000000)
  have hx183 : Bounds (144782377879 / 1000000000000) (144782379979 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(933027 / 1000000)
  have hx184 : Bounds (36152660369 / 250000000000) (146659829977 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((933027 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(934141 / 1000000)
  have hx185 : Bounds (5791332051 / 40000000000) (9177183527 / 62500000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((934141 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * (H (2*m)/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * (H (2*m)/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx96.1])
  have hcEq : biasE c = x141 * c := by
    have he := Reflection.regularContact_equation (x3 / x96)
    have hcdef : c = Reflection.regularContact (x3 / x96) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x96 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x96 := by linarith [hx96.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (933027 / 1000000) (934141 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (933027 / 1000000) ≤ (146659829977 / 1000000000000) := hx184.2
      have h2 : (146660138451 / 1000000000000) ≤ biasE (933027 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (934141 / 1000000) ≤ (144782379979 / 1000000000000) := hx183.2
      have h2 : (5791332051 / 40000000000) ≤ x141 * (934141 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1934597 / 1000000) (60489 / 31250) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-29239 / 31250) (-934597 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (2011 / 31250) (65403 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (2011 / 31250) (65403 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (7644909254927 / 500000000000) (15539532570861 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (7394909254927 / 250000000000) (15039532570861 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (7394909254927 / 250000000000) (15039532570861 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (3387086183 / 1000000000) (1701914711 / 500000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (3387086183 / 2000000000) (1701914711 / 1000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (3387086183 / 2000000000) (1701914711 / 1000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1933027 / 1000000) (1934141 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-934141 / 1000000) (-933027 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (65859 / 1000000) (66973 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (65859 / 1000000) (66973 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (14931390261747 / 1000000000000) (7591976798919 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (14431390261747 / 500000000000) (7341976798919 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (14431390261747 / 500000000000) (7341976798919 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (3362552891 / 1000000000) (422487811 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (3362552891 / 2000000000) (422487811 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (3362552891 / 2000000000) (422487811 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (21456338969 / 62500000000) (173980151137 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (142228315973 / 500000000000) (72005210683 / 250000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-72005210683 / 250000000000) (-142228315973 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (13820145193 / 250000000000) (7937958791 / 125000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (13820145193 / 250000000000) (7937958791 / 125000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (791390146343 / 500000000000) (796196547759 / 500000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-796196547759 / 500000000000) (-791390146343 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-768556257373 / 500000000000) (-759638311179 / 500000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-768556257373 / 500000000000) (-759638311179 / 500000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1540338193467 / 1000000000000) (387698580313 / 250000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (3225678721 / 1000000000000) (15758849447 / 500000000000) x218 := by
    apply bounds_add hx216 hx217 <;> norm_num
  have hpos : 0 < x218 := lt_of_lt_of_le (by norm_num) hx218.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x96)
        - (1 - 2*entropyInverse (H (2*m)/2)) *
            SmallMean.A (1 - 2*entropyInverse (H (2*m)/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*(H (2*m)/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (527 / 12800) (1073 / 25600) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (527 / 12800) ≤ m → m ≤ (1073 / 25600) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153

end


