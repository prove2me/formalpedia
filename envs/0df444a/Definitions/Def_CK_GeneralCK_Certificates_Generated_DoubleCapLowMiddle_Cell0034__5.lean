-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0034__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0034__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:07:49.068668+00:00
-- url     : https://prove2.me/theorems/3f0b9a8e-de19-482f-901e-b870acdddc51
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0034 (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0035, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0036, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0037, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0038).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0031Logs__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0036Logs__4

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (2561 / 204800) (129 / 10240) m) :
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
  have hx0 : Bounds (2561 / 102400) (129 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-129 / 5120) (-2561 / 102400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (4991 / 5120) (99839 / 102400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (4991 / 5120) (99839 / 102400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (2561 / 51200) (129 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-129 / 2560) (-2561 / 51200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2431 / 2560) (48639 / 51200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (2431 / 2560) (48639 / 51200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(99839 / 102400)
  have hx9 : Bounds (202239 / 102400) (202239 / 102400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99839 / 102400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(99839 / 102400)
  have hx10 : Bounds (202239 / 102400) (202239 / 102400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99839 / 102400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (680563453 / 1000000000) (340281727 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (1344106173547 / 1000000000000) (1344106175523 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(99839 / 102400)
  have hx13 : Bounds (-99839 / 102400) (-99839 / 102400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99839 / 102400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (2561 / 102400) (2561 / 102400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(99839 / 102400)
  have hx15 : Bounds (2561 / 102400) (2561 / 102400) x15 := by
    exact hx14
  let x16 : ℝ := -(99839 / 102400)
  have hx16 : Bounds (-99839 / 102400) (-99839 / 102400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99839 / 102400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (2561 / 102400) (2561 / 102400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(99839 / 102400)
  have hx18 : Bounds (2561 / 102400) (2561 / 102400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-922122227 / 250000000) (-1844244451 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-922482431 / 10000000000) (-92248242949 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1251857930447 / 1000000000000) (625928966287 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (625928965223 / 1000000000000) (625928966287 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (625928965223 / 1000000000000) (625928966287 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-625928966287 / 1000000000000) (-625928965223 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (67218213713 / 1000000000000) (67218215777 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (67218213713 / 1000000000000) (67218215777 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (99839 / 102400)
  have hx28 : Bounds (67218213713 / 1000000000000) (67218215777 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(4991 / 5120)
  have hx30 : Bounds (10111 / 5120) (10111 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4991 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(4991 / 5120)
  have hx31 : Bounds (10111 / 5120) (10111 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4991 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (680469501 / 1000000000) (340234751 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (53751774411 / 40000000000) (1343794362251 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(4991 / 5120)
  have hx34 : Bounds (-4991 / 5120) (-4991 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4991 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (129 / 5120) (129 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(4991 / 5120)
  have hx36 : Bounds (129 / 5120) (129 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(4991 / 5120)
  have hx37 : Bounds (-4991 / 5120) (-4991 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4991 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (129 / 5120) (129 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(4991 / 5120)
  have hx39 : Bounds (129 / 5120) (129 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-920274329 / 250000000) (-368109731 / 100000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-4637319861 / 50000000000) (-23186599267 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (250209592611 / 200000000000) (1251047965183 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (625523981527 / 1000000000000) (2443453057 / 3906250000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (625523981527 / 1000000000000) (2443453057 / 3906250000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-2443453057 / 3906250000) (-625523981527 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (2113224919 / 31250000000) (67623199473 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (2113224919 / 31250000000) (67623199473 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (4991 / 5120)
  have hx49 : Bounds (2113224919 / 31250000000) (67623199473 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (67218213713 / 1000000000000) (67623199473 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(48639 / 51200)
  have hx52 : Bounds (99839 / 51200) (99839 / 51200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48639 / 51200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(48639 / 51200)
  have hx53 : Bounds (99839 / 51200) (99839 / 51200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48639 / 51200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (166954839 / 250000000) (667819357 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1302234700853 / 1000000000000) (325558675701 / 250000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(48639 / 51200)
  have hx56 : Bounds (-48639 / 51200) (-48639 / 51200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48639 / 51200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2561 / 51200) (2561 / 51200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(48639 / 51200)
  have hx58 : Bounds (2561 / 51200) (2561 / 51200) x58 := by
    exact hx57
  let x59 : ℝ := -(48639 / 51200)
  have hx59 : Bounds (-48639 / 51200) (-48639 / 51200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48639 / 51200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2561 / 51200) (2561 / 51200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(48639 / 51200)
  have hx61 : Bounds (2561 / 51200) (2561 / 51200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2995341727 / 1000000000) (-1497670861 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-149825589119 / 1000000000000) (-37456397217 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (576204555867 / 500000000000) (72025569621 / 62500000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (576204555867 / 1000000000000) (72025569621 / 125000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (576204555867 / 1000000000000) (72025569621 / 125000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-72025569621 / 125000000000) (-576204555867 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (14617827879 / 125000000000) (116942625133 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (14617827879 / 125000000000) (116942625133 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (48639 / 51200)
  have hx71 : Bounds (14617827879 / 125000000000) (116942625133 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2431 / 2560)
  have hx73 : Bounds (4991 / 2560) (4991 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2431 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2431 / 2560)
  have hx74 : Bounds (4991 / 2560) (4991 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2431 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (667629031 / 1000000000) (83453629 / 125000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1301615817859 / 1000000000000) (130161581981 / 100000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2431 / 2560)
  have hx77 : Bounds (-2431 / 2560) (-2431 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2431 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (129 / 2560) (129 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2431 / 2560)
  have hx79 : Bounds (129 / 2560) (129 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(2431 / 2560)
  have hx80 : Bounds (-2431 / 2560) (-2431 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2431 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (129 / 2560) (129 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2431 / 2560)
  have hx82 : Bounds (129 / 2560) (129 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-597590027 / 200000000) (-298795013 / 100000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-37641168693 / 250000000000) (-150564674519 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (1151051143087 / 1000000000000) (1151051145291 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (575525571543 / 1000000000000) (287762786323 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (575525571543 / 1000000000000) (287762786323 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-287762786323 / 500000000000) (-575525571543 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (58810803677 / 500000000000) (117621609457 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (58810803677 / 500000000000) (117621609457 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2431 / 2560)
  have hx92 : Bounds (58810803677 / 500000000000) (117621609457 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (14617827879 / 125000000000) (117621609457 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (14617827879 / 250000000000) (58810804729 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (14617827879 / 250000000000) (58810804729 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(978769 / 1000000)
  have hx98 : Bounds (1978769 / 1000000) (1978769 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978769 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(978769 / 1000000)
  have hx99 : Bounds (1978769 / 1000000) (1978769 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978769 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (341237467 / 500000000) (136494987 / 200000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (337615060669 / 250000000000) (84403765291 / 62500000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(978769 / 1000000)
  have hx102 : Bounds (-978769 / 1000000) (-978769 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978769 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (21231 / 1000000) (21231 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(978769 / 1000000)
  have hx104 : Bounds (21231 / 1000000) (21231 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(978769 / 1000000)
  have hx105 : Bounds (-978769 / 1000000) (-978769 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978769 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (21231 / 1000000) (21231 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(978769 / 1000000)
  have hx107 : Bounds (21231 / 1000000) (21231 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-481536613 / 125000000) (-1926146449 / 500000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-16357606129 / 200000000000) (-81788030517 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1268672212031 / 1000000000000) (1268672214139 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (126867221203 / 200000000000) (63433610707 / 100000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (126867221203 / 200000000000) (63433610707 / 100000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-63433610707 / 100000000000) (-126867221203 / 200000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (5881107293 / 100000000000) (11762214997 / 200000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (5881107293 / 100000000000) (11762214997 / 200000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (978769 / 1000000)
  have hx117 : Bounds (5881107293 / 100000000000) (11762214997 / 200000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(978919 / 1000000)
  have hx119 : Bounds (1978919 / 1000000) (1978919 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978919 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(978919 / 1000000)
  have hx120 : Bounds (1978919 / 1000000) (1978919 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978919 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (42659421 / 62500000) (682550737 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (675356309967 / 500000000000) (675356310957 / 500000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(978919 / 1000000)
  have hx123 : Bounds (-978919 / 1000000) (-978919 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978919 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (21081 / 1000000) (21081 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(978919 / 1000000)
  have hx125 : Bounds (21081 / 1000000) (21081 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(978919 / 1000000)
  have hx126 : Bounds (-978919 / 1000000) (-978919 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978919 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (21081 / 1000000) (21081 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(978919 / 1000000)
  have hx128 : Bounds (21081 / 1000000) (21081 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-3859383121 / 1000000000) (-771876623 / 200000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-40679827787 / 500000000000) (-81359655447 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (31733824109 / 25000000000) (1269352966467 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (31733824109 / 50000000000) (317338241617 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (31733824109 / 50000000000) (317338241617 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-317338241617 / 500000000000) (-31733824109 / 50000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (29235348383 / 500000000000) (2923534941 / 50000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (29235348383 / 500000000000) (2923534941 / 50000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (978919 / 1000000)
  have hx138 : Bounds (29235348383 / 500000000000) (2923534941 / 50000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (978769 / 1000000) (978919 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (978919 / 1000000) ≤ (2923534941 / 50000000000) := hx138.2
      have h2 : (14617827879 / 250000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (58810804729 / 1000000000000) := hx96.2
      have h2 : (5881107293 / 100000000000) ≤ biasE (978769 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (102565129859 / 100000000000) (1025846523743 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (29985588293 / 500000000000) (6033085959 / 100000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (29985588293 / 500000000000) (6033085959 / 100000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(489333 / 500000)
  have hx143 : Bounds (989333 / 500000) (989333 / 500000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489333 / 500000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(489333 / 500000)
  have hx144 : Bounds (989333 / 500000) (989333 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489333 / 500000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (4265143 / 6250000) (682422881 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (675143475139 / 500000000000) (1350286952257 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(489333 / 500000)
  have hx147 : Bounds (-489333 / 500000) (-489333 / 500000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489333 / 500000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (10667 / 500000) (10667 / 500000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(489333 / 500000)
  have hx149 : Bounds (10667 / 500000) (10667 / 500000) x149 := by
    exact hx148
  let x150 : ℝ := -(489333 / 500000)
  have hx150 : Bounds (-489333 / 500000) (-489333 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489333 / 500000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (10667 / 500000) (10667 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(489333 / 500000)
  have hx152 : Bounds (10667 / 500000) (10667 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3847453237 / 1000000000) (-3847453231 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-82081567359 / 1000000000000) (-8208156723 / 100000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1268205382919 / 1000000000000) (1268205385027 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (634102691459 / 1000000000000) (317051346257 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (634102691459 / 1000000000000) (317051346257 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-317051346257 / 500000000000) (-634102691459 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (29522243743 / 500000000000) (59044489541 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (29522243743 / 500000000000) (59044489541 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (489333 / 500000)
  have hx162 : Bounds (29522243743 / 500000000000) (59044489541 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(489409 / 500000)
  have hx164 : Bounds (989409 / 500000) (989409 / 500000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489409 / 500000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(489409 / 500000)
  have hx165 : Bounds (989409 / 500000) (989409 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489409 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (42656231 / 62500000) (682499697 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1350542683439 / 1000000000000) (1350542685419 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(489409 / 500000)
  have hx168 : Bounds (-489409 / 500000) (-489409 / 500000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489409 / 500000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (10591 / 500000) (10591 / 500000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(489409 / 500000)
  have hx170 : Bounds (10591 / 500000) (10591 / 500000) x170 := by
    exact hx169
  let x171 : ℝ := -(489409 / 500000)
  have hx171 : Bounds (-489409 / 500000) (-489409 / 500000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489409 / 500000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (10591 / 500000) (10591 / 500000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(489409 / 500000)
  have hx173 : Bounds (10591 / 500000) (10591 / 500000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-3854603517 / 1000000000) (-3854603511 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-40824105849 / 500000000000) (-8164821157 / 100000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1268894471741 / 1000000000000) (1268894473849 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (63444723587 / 100000000000) (25377889477 / 40000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (63444723587 / 100000000000) (25377889477 / 40000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-25377889477 / 40000000000) (-63444723587 / 100000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (2347997723 / 40000000000) (5869994513 / 100000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (2347997723 / 40000000000) (5869994513 / 100000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (489409 / 500000)
  have hx183 : Bounds (2347997723 / 40000000000) (5869994513 / 100000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(489333 / 500000)
  have hx184 : Bounds (3668234469 / 62500000000) (7380470129 / 125000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((489333 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(489409 / 500000)
  have hx185 : Bounds (58700867123 / 1000000000000) (59052931323 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((489409 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (489333 / 500000) (489409 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (489333 / 500000) ≤ (7380470129 / 125000000000) := hx184.2
      have h2 : (29522243743 / 500000000000) ≤ biasE (489333 / 500000) := hx162.1
      linarith
    · have h1 : biasE (489409 / 500000) ≤ (5869994513 / 100000000000) := hx183.2
      have h2 : (58700867123 / 1000000000000) ≤ x141 * (489409 / 500000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1978769 / 1000000) (1978919 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-978919 / 1000000) (-978769 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (21081 / 1000000) (21231 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (21081 / 1000000) (21231 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (11775234327163 / 250000000000) (47436079882359 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (11650234327163 / 125000000000) (46936079882359 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (11650234327163 / 125000000000) (46936079882359 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (566845979 / 125000000) (4541933857 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (566845979 / 250000000) (4541933857 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (566845979 / 250000000) (4541933857 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (989333 / 500000) (989409 / 500000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-489409 / 500000) (-489333 / 500000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (10591 / 500000) (10667 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (10591 / 500000) (10667 / 500000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (5859191900253 / 125000000000) (47209895194033 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (5796691900253 / 62500000000) (46709895194033 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (5796691900253 / 62500000000) (46709895194033 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (4529876111 / 1000000000) (2268551607 / 500000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (4529876111 / 2000000000) (2268551607 / 1000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (4529876111 / 2000000000) (2268551607 / 1000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (67218213713 / 500000000000) (67623199473 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (14617827879 / 125000000000) (58810804729 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-58810804729 / 500000000000) (-14617827879 / 125000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (1050926123 / 62500000000) (9151887957 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (1050926123 / 62500000000) (9151887957 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2219245088079 / 1000000000000) (2223092674681 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2223092674681 / 1000000000000) (-2219245088079 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2206277856713 / 1000000000000) (-440188262433 / 200000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2206277856713 / 1000000000000) (-440188262433 / 200000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1103936116699 / 500000000000) (2211815663001 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (318875337 / 200000000000) (2718587709 / 250000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (2561 / 204800) (129 / 10240) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (2561 / 204800) ≤ m → m ≤ (129 / 10240) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (129 / 10240) (2599 / 204800) m) :
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
  have hx0 : Bounds (129 / 5120) (2599 / 102400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-2599 / 102400) (-129 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (99801 / 102400) (4991 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (99801 / 102400) (4991 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (129 / 2560) (2599 / 51200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-2599 / 51200) (-129 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (48601 / 51200) (2431 / 2560) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (48601 / 51200) (2431 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(4991 / 5120)
  have hx9 : Bounds (10111 / 5120) (10111 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4991 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(4991 / 5120)
  have hx10 : Bounds (10111 / 5120) (10111 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4991 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (680469501 / 1000000000) (340234751 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (53751774411 / 40000000000) (1343794362251 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(4991 / 5120)
  have hx13 : Bounds (-4991 / 5120) (-4991 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4991 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (129 / 5120) (129 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(4991 / 5120)
  have hx15 : Bounds (129 / 5120) (129 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(4991 / 5120)
  have hx16 : Bounds (-4991 / 5120) (-4991 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4991 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (129 / 5120) (129 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(4991 / 5120)
  have hx18 : Bounds (129 / 5120) (129 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-920274329 / 250000000) (-368109731 / 100000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-4637319861 / 50000000000) (-23186599267 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (250209592611 / 200000000000) (1251047965183 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (625523981527 / 1000000000000) (2443453057 / 3906250000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (625523981527 / 1000000000000) (2443453057 / 3906250000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-2443453057 / 3906250000) (-625523981527 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (2113224919 / 31250000000) (67623199473 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (2113224919 / 31250000000) (67623199473 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (4991 / 5120)
  have hx28 : Bounds (2113224919 / 31250000000) (67623199473 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(99801 / 102400)
  have hx30 : Bounds (202201 / 102400) (202201 / 102400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99801 / 102400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(99801 / 102400)
  have hx31 : Bounds (202201 / 102400) (202201 / 102400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99801 / 102400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (680375539 / 1000000000) (34018777 / 50000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (671741281061 / 500000000000) (671741282049 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(99801 / 102400)
  have hx34 : Bounds (-99801 / 102400) (-99801 / 102400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99801 / 102400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (2599 / 102400) (2599 / 102400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(99801 / 102400)
  have hx36 : Bounds (2599 / 102400) (2599 / 102400) x36 := by
    exact hx35
  let x37 : ℝ := -(99801 / 102400)
  have hx37 : Bounds (-99801 / 102400) (-99801 / 102400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99801 / 102400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (2599 / 102400) (2599 / 102400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(99801 / 102400)
  have hx39 : Bounds (2599 / 102400) (2599 / 102400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-91843999 / 25000000) (-1836879977 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-93243184923 / 1000000000000) (-93243184769 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1250239377199 / 1000000000000) (1250239379329 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (625119688599 / 1000000000000) (125023937933 / 200000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (625119688599 / 1000000000000) (125023937933 / 200000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-125023937933 / 200000000000) (-625119688599 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (13605498067 / 200000000000) (68027492401 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (13605498067 / 200000000000) (68027492401 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (99801 / 102400)
  have hx49 : Bounds (13605498067 / 200000000000) (68027492401 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (2113224919 / 31250000000) (68027492401 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2431 / 2560)
  have hx52 : Bounds (4991 / 2560) (4991 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2431 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2431 / 2560)
  have hx53 : Bounds (4991 / 2560) (4991 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2431 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (667629031 / 1000000000) (83453629 / 125000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1301615817859 / 1000000000000) (130161581981 / 100000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2431 / 2560)
  have hx56 : Bounds (-2431 / 2560) (-2431 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2431 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (129 / 2560) (129 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2431 / 2560)
  have hx58 : Bounds (129 / 2560) (129 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(2431 / 2560)
  have hx59 : Bounds (-2431 / 2560) (-2431 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2431 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (129 / 2560) (129 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2431 / 2560)
  have hx61 : Bounds (129 / 2560) (129 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-597590027 / 200000000) (-298795013 / 100000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-37641168693 / 250000000000) (-150564674519 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1151051143087 / 1000000000000) (1151051145291 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (575525571543 / 1000000000000) (287762786323 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (575525571543 / 1000000000000) (287762786323 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-287762786323 / 500000000000) (-575525571543 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (58810803677 / 500000000000) (117621609457 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (58810803677 / 500000000000) (117621609457 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2431 / 2560)
  have hx71 : Bounds (58810803677 / 500000000000) (117621609457 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(48601 / 51200)
  have hx73 : Bounds (99801 / 51200) (99801 / 51200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48601 / 51200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(48601 / 51200)
  have hx74 : Bounds (99801 / 51200) (99801 / 51200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48601 / 51200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (667438671 / 1000000000) (41714917 / 62500000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1300997007899 / 1000000000000) (26019940197 / 20000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(48601 / 51200)
  have hx77 : Bounds (-48601 / 51200) (-48601 / 51200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48601 / 51200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2599 / 51200) (2599 / 51200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(48601 / 51200)
  have hx79 : Bounds (2599 / 51200) (2599 / 51200) x79 := by
    exact hx78
  let x80 : ℝ := -(48601 / 51200)
  have hx80 : Bounds (-48601 / 51200) (-48601 / 51200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48601 / 51200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2599 / 51200) (2599 / 51200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(48601 / 51200)
  have hx82 : Bounds (2599 / 51200) (2599 / 51200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2980612779 / 1000000000) (-1490306387 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-151301027591 / 1000000000000) (-18912628417 / 125000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (287423995077 / 250000000000) (574847991257 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (287423995077 / 500000000000) (574847991257 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (287423995077 / 500000000000) (574847991257 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-574847991257 / 1000000000000) (-287423995077 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (118299188743 / 1000000000000) (59149595423 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (118299188743 / 1000000000000) (59149595423 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (48601 / 51200)
  have hx92 : Bounds (118299188743 / 1000000000000) (59149595423 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (58810803677 / 500000000000) (59149595423 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (58810803677 / 1000000000000) (59149595423 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (58810803677 / 1000000000000) (59149595423 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(978619 / 1000000)
  have hx98 : Bounds (1978619 / 1000000) (1978619 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978619 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(978619 / 1000000)
  have hx99 : Bounds (1978619 / 1000000) (1978619 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978619 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (341199563 / 500000000) (682399127 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (675103938143 / 500000000000) (675103939133 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(978619 / 1000000)
  have hx102 : Bounds (-978619 / 1000000) (-978619 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978619 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (21381 / 1000000) (21381 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(978619 / 1000000)
  have hx104 : Bounds (21381 / 1000000) (21381 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(978619 / 1000000)
  have hx105 : Bounds (-978619 / 1000000) (-978619 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978619 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (21381 / 1000000) (21381 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(978619 / 1000000)
  have hx107 : Bounds (21381 / 1000000) (21381 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-961313151 / 250000000) (-1922626299 / 500000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-82215345927 / 1000000000000) (-82215345797 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1267992530359 / 1000000000000) (1267992532469 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (633996265179 / 1000000000000) (126799253247 / 200000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (633996265179 / 1000000000000) (126799253247 / 200000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-126799253247 / 200000000000) (-633996265179 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (11830182753 / 200000000000) (59150915821 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (11830182753 / 200000000000) (59150915821 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (978619 / 1000000)
  have hx117 : Bounds (11830182753 / 200000000000) (59150915821 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(97877 / 100000)
  have hx119 : Bounds (197877 / 100000) (197877 / 100000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97877 / 100000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(97877 / 100000)
  have hx120 : Bounds (197877 / 100000) (197877 / 100000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97877 / 100000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (682475439 / 1000000000) (8530943 / 12500000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (135046192443 / 100000000000) (1350461926409 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(97877 / 100000)
  have hx123 : Bounds (-97877 / 100000) (-97877 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97877 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (2123 / 100000) (2123 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(97877 / 100000)
  have hx125 : Bounds (2123 / 100000) (2123 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := -(97877 / 100000)
  have hx126 : Bounds (-97877 / 100000) (-97877 / 100000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97877 / 100000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (2123 / 100000) (2123 / 100000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(97877 / 100000)
  have hx128 : Bounds (2123 / 100000) (2123 / 100000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1926170003 / 500000000) (-192617 / 50000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-10223147291 / 125000000000) (-408925891 / 5000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (634338373051 / 500000000000) (1268676748209 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (634338373051 / 1000000000000) (126867674821 / 200000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (634338373051 / 1000000000000) (126867674821 / 200000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-126867674821 / 200000000000) (-634338373051 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (11761761179 / 200000000000) (58808807949 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (11761761179 / 200000000000) (58808807949 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (97877 / 100000)
  have hx138 : Bounds (11761761179 / 200000000000) (58808807949 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (978619 / 1000000) (97877 / 100000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (97877 / 100000) ≤ (58808807949 / 1000000000000) := hx138.2
      have h2 : (58810803677 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (59149595423 / 1000000000000) := hx96.2
      have h2 : (11830182753 / 200000000000) ≤ biasE (978619 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (512923261871 / 500000000000) (1026041823229 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (6033085851 / 100000000000) (15172489683 / 250000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (6033085851 / 100000000000) (15172489683 / 250000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(195703 / 200000)
  have hx143 : Bounds (395703 / 200000) (395703 / 200000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((195703 / 200000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(195703 / 200000)
  have hx144 : Bounds (395703 / 200000) (395703 / 200000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((195703 / 200000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (682346563 / 1000000000) (170586641 / 250000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1350032910093 / 1000000000000) (1350032912073 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(195703 / 200000)
  have hx147 : Bounds (-195703 / 200000) (-195703 / 200000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((195703 / 200000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (4297 / 200000) (4297 / 200000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(195703 / 200000)
  have hx149 : Bounds (4297 / 200000) (4297 / 200000) x149 := by
    exact hx148
  let x150 : ℝ := -(195703 / 200000)
  have hx150 : Bounds (-195703 / 200000) (-195703 / 200000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((195703 / 200000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (4297 / 200000) (4297 / 200000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(195703 / 200000)
  have hx152 : Bounds (4297 / 200000) (4297 / 200000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-480050033 / 125000000) (-1920200129 / 500000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-82510999673 / 1000000000000) (-82510999543 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (63376095521 / 50000000000) (126752191253 / 100000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (63376095521 / 100000000000) (126752191253 / 200000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (63376095521 / 100000000000) (126752191253 / 200000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-126752191253 / 200000000000) (-63376095521 / 100000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (11877244747 / 200000000000) (5938622579 / 100000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (11877244747 / 200000000000) (5938622579 / 100000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (195703 / 200000)
  have hx162 : Bounds (11877244747 / 200000000000) (5938622579 / 100000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(978667 / 1000000)
  have hx164 : Bounds (1978667 / 1000000) (1978667 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978667 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(978667 / 1000000)
  have hx165 : Bounds (1978667 / 1000000) (1978667 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978667 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (136484677 / 200000000) (341211693 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1350288631927 / 1000000000000) (1350288633907 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(978667 / 1000000)
  have hx168 : Bounds (-978667 / 1000000) (-978667 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978667 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (21333 / 1000000) (21333 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(978667 / 1000000)
  have hx170 : Bounds (21333 / 1000000) (21333 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(978667 / 1000000)
  have hx171 : Bounds (-978667 / 1000000) (-978667 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978667 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (21333 / 1000000) (21333 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(978667 / 1000000)
  have hx173 : Bounds (21333 / 1000000) (21333 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-240468757 / 62500000) (-1923750053 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-8207871989 / 100000000000) (-82078719761 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1268209912037 / 1000000000000) (634104957073 / 500000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (317052478009 / 500000000000) (634104957073 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (317052478009 / 500000000000) (634104957073 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-634104957073 / 1000000000000) (-317052478009 / 500000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (59042222927 / 1000000000000) (29521112491 / 500000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (59042222927 / 1000000000000) (29521112491 / 500000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (978667 / 1000000)
  have hx183 : Bounds (59042222927 / 1000000000000) (29521112491 / 500000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(195703 / 200000)
  have hx184 : Bounds (29517325007 / 500000000000) (59386034969 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((195703 / 200000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(978667 / 1000000)
  have hx185 : Bounds (11808764061 / 200000000000) (59395259843 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((978667 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (195703 / 200000) (978667 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (195703 / 200000) ≤ (59386034969 / 1000000000000) := hx184.2
      have h2 : (11877244747 / 200000000000) ≤ biasE (195703 / 200000) := hx162.1
      linarith
    · have h1 : biasE (978667 / 1000000) ≤ (29521112491 / 500000000000) := hx183.2
      have h2 : (11808764061 / 200000000000) ≤ x141 * (978667 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1978619 / 1000000) (197877 / 100000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-97877 / 100000) (-978619 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (2123 / 100000) (21381 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (2123 / 100000) (21381 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (2923156073149 / 62500000000) (47103155911447 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (2891906073149 / 31250000000) (46603155911447 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (2891906073149 / 31250000000) (46603155911447 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (181106069 / 40000000) (2267407723 / 500000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (181106069 / 80000000) (2267407723 / 1000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (181106069 / 80000000) (2267407723 / 1000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (395703 / 200000) (1978667 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-978667 / 1000000) (-195703 / 200000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (21333 / 1000000) (4297 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (21333 / 1000000) (4297 / 200000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (46544100535257 / 1000000000000) (1171893310833 / 25000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (46044100535257 / 500000000000) (1159393310833 / 12500000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (46044100535257 / 500000000000) (1159393310833 / 12500000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (4522746821 / 1000000000) (2264961749 / 500000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (4522746821 / 2000000000) (2264961749 / 1000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (4522746821 / 2000000000) (2264961749 / 1000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (2113224919 / 15625000000) (68027492401 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (58810803677 / 500000000000) (59149595423 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-59149595423 / 500000000000) (-58810803677 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (1694720397 / 100000000000) (2304172181 / 125000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (1694720397 / 100000000000) (2304172181 / 125000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2215423001733 / 1000000000000) (2219270657041 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2219270657041 / 1000000000000) (-2215423001733 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2202323453071 / 1000000000000) (-439397924857 / 200000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2202323453071 / 1000000000000) (-439397924857 / 200000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2203977809973 / 1000000000000) (1103947664967 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (827178451 / 500000000000) (10905705649 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (129 / 10240) (2599 / 204800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (129 / 10240) ≤ m → m ≤ (2599 / 204800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (2599 / 204800) (1309 / 102400) m) :
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
  have hx0 : Bounds (2599 / 102400) (1309 / 51200) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1309 / 51200) (-2599 / 102400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (49891 / 51200) (99801 / 102400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (49891 / 51200) (99801 / 102400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (2599 / 51200) (1309 / 25600) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1309 / 25600) (-2599 / 51200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (24291 / 25600) (48601 / 51200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (24291 / 25600) (48601 / 51200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(99801 / 102400)
  have hx9 : Bounds (202201 / 102400) (202201 / 102400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99801 / 102400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(99801 / 102400)
  have hx10 : Bounds (202201 / 102400) (202201 / 102400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99801 / 102400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (680375539 / 1000000000) (34018777 / 50000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (671741281061 / 500000000000) (671741282049 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(99801 / 102400)
  have hx13 : Bounds (-99801 / 102400) (-99801 / 102400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99801 / 102400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (2599 / 102400) (2599 / 102400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(99801 / 102400)
  have hx15 : Bounds (2599 / 102400) (2599 / 102400) x15 := by
    exact hx14
  let x16 : ℝ := -(99801 / 102400)
  have hx16 : Bounds (-99801 / 102400) (-99801 / 102400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99801 / 102400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (2599 / 102400) (2599 / 102400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(99801 / 102400)
  have hx18 : Bounds (2599 / 102400) (2599 / 102400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-91843999 / 25000000) (-1836879977 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-93243184923 / 1000000000000) (-93243184769 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1250239377199 / 1000000000000) (1250239379329 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (625119688599 / 1000000000000) (125023937933 / 200000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (625119688599 / 1000000000000) (125023937933 / 200000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-125023937933 / 200000000000) (-625119688599 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (13605498067 / 200000000000) (68027492401 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (13605498067 / 200000000000) (68027492401 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (99801 / 102400)
  have hx28 : Bounds (13605498067 / 200000000000) (68027492401 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(49891 / 51200)
  have hx30 : Bounds (101091 / 51200) (101091 / 51200) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49891 / 51200) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(49891 / 51200)
  have hx31 : Bounds (101091 / 51200) (101091 / 51200) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49891 / 51200) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (680281569 / 1000000000) (68028157 / 100000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (671585391521 / 500000000000) (1343170785017 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(49891 / 51200)
  have hx34 : Bounds (-49891 / 51200) (-49891 / 51200) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49891 / 51200) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1309 / 51200) (1309 / 51200) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(49891 / 51200)
  have hx36 : Bounds (1309 / 51200) (1309 / 51200) x36 := by
    exact hx35
  let x37 : ℝ := -(49891 / 51200)
  have hx37 : Bounds (-49891 / 51200) (-49891 / 51200) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49891 / 51200) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1309 / 51200) (1309 / 51200) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(49891 / 51200)
  have hx39 : Bounds (1309 / 51200) (1309 / 51200) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-229154753 / 62500000) (-1833238021 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-1874772323 / 20000000000) (-18747723199 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (312358041723 / 250000000000) (624716084511 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (312358041723 / 500000000000) (624716084511 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (312358041723 / 500000000000) (624716084511 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-624716084511 / 1000000000000) (-312358041723 / 500000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (68431095489 / 1000000000000) (34215548777 / 500000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (68431095489 / 1000000000000) (34215548777 / 500000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (49891 / 51200)
  have hx49 : Bounds (68431095489 / 1000000000000) (34215548777 / 500000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (13605498067 / 200000000000) (34215548777 / 500000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(48601 / 51200)
  have hx52 : Bounds (99801 / 51200) (99801 / 51200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48601 / 51200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(48601 / 51200)
  have hx53 : Bounds (99801 / 51200) (99801 / 51200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48601 / 51200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (667438671 / 1000000000) (41714917 / 62500000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1300997007899 / 1000000000000) (26019940197 / 20000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(48601 / 51200)
  have hx56 : Bounds (-48601 / 51200) (-48601 / 51200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48601 / 51200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2599 / 51200) (2599 / 51200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(48601 / 51200)
  have hx58 : Bounds (2599 / 51200) (2599 / 51200) x58 := by
    exact hx57
  let x59 : ℝ := -(48601 / 51200)
  have hx59 : Bounds (-48601 / 51200) (-48601 / 51200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48601 / 51200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2599 / 51200) (2599 / 51200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(48601 / 51200)
  have hx61 : Bounds (2599 / 51200) (2599 / 51200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2980612779 / 1000000000) (-1490306387 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-151301027591 / 1000000000000) (-18912628417 / 125000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (287423995077 / 250000000000) (574847991257 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (287423995077 / 500000000000) (574847991257 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (287423995077 / 500000000000) (574847991257 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-574847991257 / 1000000000000) (-287423995077 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (118299188743 / 1000000000000) (59149595423 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (118299188743 / 1000000000000) (59149595423 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (48601 / 51200)
  have hx71 : Bounds (118299188743 / 1000000000000) (59149595423 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(24291 / 25600)
  have hx73 : Bounds (49891 / 25600) (49891 / 25600) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24291 / 25600) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(24291 / 25600)
  have hx74 : Bounds (49891 / 25600) (49891 / 25600) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24291 / 25600) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (333624137 / 500000000) (26689931 / 40000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (650189133557 / 500000000000) (162547283633 / 125000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(24291 / 25600)
  have hx77 : Bounds (-24291 / 25600) (-24291 / 25600) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24291 / 25600) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1309 / 25600) (1309 / 25600) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(24291 / 25600)
  have hx79 : Bounds (1309 / 25600) (1309 / 25600) x79 := by
    exact hx78
  let x80 : ℝ := -(24291 / 25600)
  have hx80 : Bounds (-24291 / 25600) (-24291 / 25600) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24291 / 25600) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1309 / 25600) (1309 / 25600) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(24291 / 25600)
  have hx82 : Bounds (1309 / 25600) (1309 / 25600) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2973328867 / 1000000000) (-1486664431 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-76017333729 / 500000000000) (-152034667201 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (143542949957 / 125000000000) (1148343601863 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (143542949957 / 250000000000) (143542950233 / 250000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (143542949957 / 250000000000) (143542950233 / 250000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-143542950233 / 250000000000) (-143542949957 / 250000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (29743844767 / 250000000000) (29743845293 / 250000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (29743844767 / 250000000000) (29743845293 / 250000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (24291 / 25600)
  have hx92 : Bounds (29743844767 / 250000000000) (29743845293 / 250000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (118299188743 / 1000000000000) (29743845293 / 250000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (59149594371 / 1000000000000) (29743845293 / 500000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (59149594371 / 1000000000000) (29743845293 / 500000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(97847 / 100000)
  have hx98 : Bounds (197847 / 100000) (197847 / 100000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97847 / 100000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(97847 / 100000)
  have hx99 : Bounds (197847 / 100000) (197847 / 100000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97847 / 100000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (341161909 / 500000000) (682323819 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (674978602099 / 500000000000) (1349957206177 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(97847 / 100000)
  have hx102 : Bounds (-97847 / 100000) (-97847 / 100000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97847 / 100000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (2153 / 100000) (2153 / 100000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(97847 / 100000)
  have hx104 : Bounds (2153 / 100000) (2153 / 100000) x104 := by
    exact hx103
  let x105 : ℝ := -(97847 / 100000)
  have hx105 : Bounds (-97847 / 100000) (-97847 / 100000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97847 / 100000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (2153 / 100000) (2153 / 100000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(97847 / 100000)
  have hx107 : Bounds (2153 / 100000) (2153 / 100000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-383830797 / 100000000) (-959576991 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-16527754119 / 200000000000) (-2582461577 / 31250000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1267318433603 / 1000000000000) (1267318435713 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (633659216801 / 1000000000000) (633659217857 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (633659216801 / 1000000000000) (633659217857 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-633659217857 / 1000000000000) (-633659216801 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (59487962143 / 1000000000000) (59487964199 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (59487962143 / 1000000000000) (59487964199 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (97847 / 100000)
  have hx117 : Bounds (59487962143 / 1000000000000) (59487964199 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(48931 / 50000)
  have hx119 : Bounds (98931 / 50000) (98931 / 50000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48931 / 50000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(48931 / 50000)
  have hx120 : Bounds (98931 / 50000) (98931 / 50000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48931 / 50000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (42649977 / 62500000) (682399633 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1350209559867 / 1000000000000) (1350209561847 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(48931 / 50000)
  have hx123 : Bounds (-48931 / 50000) (-48931 / 50000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48931 / 50000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (1069 / 50000) (1069 / 50000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(48931 / 50000)
  have hx125 : Bounds (1069 / 50000) (1069 / 50000) x125 := by
    exact hx124
  let x126 : ℝ := -(48931 / 50000)
  have hx126 : Bounds (-48931 / 50000) (-48931 / 50000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48931 / 50000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (1069 / 50000) (1069 / 50000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(48931 / 50000)
  have hx128 : Bounds (1069 / 50000) (1069 / 50000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-240331211 / 62500000) (-384529937 / 100000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-82212500659 / 1000000000000) (-8221250053 / 100000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (158499632401 / 125000000000) (1267997061317 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (158499632401 / 250000000000) (633998530659 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (158499632401 / 250000000000) (633998530659 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-633998530659 / 1000000000000) (-158499632401 / 250000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (59148649341 / 1000000000000) (14787162849 / 250000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (59148649341 / 1000000000000) (14787162849 / 250000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (48931 / 50000)
  have hx138 : Bounds (59148649341 / 1000000000000) (14787162849 / 250000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (97847 / 100000) (48931 / 50000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (48931 / 50000) ≤ (14787162849 / 250000000000) := hx138.2
      have h2 : (59149594371 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (29743845293 / 500000000000) := hx96.2
      have h2 : (59487962143 / 1000000000000) ≤ biasE (97847 / 100000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (256510455807 / 250000000000) (102623719709 / 100000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (60689957651 / 1000000000000) (61048480849 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (60689957651 / 1000000000000) (61048480849 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(978363 / 1000000)
  have hx143 : Bounds (1978363 / 1000000) (1978363 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978363 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(978363 / 1000000)
  have hx144 : Bounds (1978363 / 1000000) (1978363 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978363 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (136453947 / 200000000) (85283717 / 125000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1349777199743 / 1000000000000) (1349777201723 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(978363 / 1000000)
  have hx147 : Bounds (-978363 / 1000000) (-978363 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978363 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (21637 / 1000000) (21637 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(978363 / 1000000)
  have hx149 : Bounds (21637 / 1000000) (21637 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(978363 / 1000000)
  have hx150 : Bounds (-978363 / 1000000) (-978363 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978363 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (21637 / 1000000) (21637 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(978363 / 1000000)
  have hx152 : Bounds (21637 / 1000000) (21637 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3833350469 / 1000000000) (-3833350463 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-41471102049 / 500000000000) (-82942203967 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (253366999129 / 200000000000) (316708749439 / 250000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (316708748911 / 500000000000) (316708749439 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (316708748911 / 500000000000) (316708749439 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-316708749439 / 500000000000) (-316708748911 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (29864840561 / 500000000000) (29864841589 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (29864840561 / 500000000000) (29864841589 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (978363 / 1000000)
  have hx162 : Bounds (29864840561 / 500000000000) (29864841589 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(244629 / 250000)
  have hx164 : Bounds (494629 / 250000) (494629 / 250000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244629 / 250000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(244629 / 250000)
  have hx165 : Bounds (494629 / 250000) (494629 / 250000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244629 / 250000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (170586767 / 250000000) (682347069 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1350034591591 / 1000000000000) (135003459357 / 100000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(244629 / 250000)
  have hx168 : Bounds (-244629 / 250000) (-244629 / 250000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244629 / 250000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (5371 / 250000) (5371 / 250000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(244629 / 250000)
  have hx170 : Bounds (5371 / 250000) (5371 / 250000) x170 := by
    exact hx169
  let x171 : ℝ := -(244629 / 250000)
  have hx171 : Bounds (-244629 / 250000) (-244629 / 250000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244629 / 250000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (5371 / 250000) (5371 / 250000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(244629 / 250000)
  have hx173 : Bounds (5371 / 250000) (5371 / 250000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-384044681 / 100000000) (-960111701 / 250000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-82508159267 / 1000000000000) (-82508159137 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (316881608081 / 250000000000) (1267526434433 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (316881608081 / 500000000000) (633763217217 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (316881608081 / 500000000000) (633763217217 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-633763217217 / 1000000000000) (-316881608081 / 500000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (59383962783 / 1000000000000) (29691982419 / 500000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (59383962783 / 1000000000000) (29691982419 / 500000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (244629 / 250000)
  have hx183 : Bounds (59383962783 / 1000000000000) (29691982419 / 500000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(978363 / 1000000)
  have hx184 : Bounds (59376809037 / 1000000000000) (59727574869 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((978363 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(244629 / 250000)
  have hx185 : Bounds (296930473 / 5000000000) (59736915287 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((244629 / 250000) : ℝ)) <;> norm_num
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
  have hc : Bounds (978363 / 1000000) (244629 / 250000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (978363 / 1000000) ≤ (59727574869 / 1000000000000) := hx184.2
      have h2 : (29864840561 / 500000000000) ≤ biasE (978363 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (244629 / 250000) ≤ (29691982419 / 500000000000) := hx183.2
      have h2 : (296930473 / 5000000000) ≤ x141 * (244629 / 250000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (197847 / 100000) (98931 / 50000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-48931 / 50000) (-97847 / 100000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (1069 / 50000) (2153 / 100000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (1069 / 50000) (2153 / 100000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (2322340919647 / 50000000000) (9354536950421 / 200000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (2297340919647 / 25000000000) (9254536950421 / 100000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (2297340919647 / 25000000000) (9254536950421 / 100000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (2260315891 / 500000000) (4527699009 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (2260315891 / 1000000000) (4527699009 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (2260315891 / 1000000000) (4527699009 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1978363 / 1000000) (494629 / 250000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-244629 / 250000) (-978363 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (5371 / 250000) (21637 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (5371 / 250000) (21637 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (46217128067661 / 1000000000000) (11636566747347 / 250000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (45717128067661 / 500000000000) (11511566747347 / 125000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (45717128067661 / 500000000000) (11511566747347 / 125000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (2257810099 / 500000000) (4522793879 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (2257810099 / 1000000000) (4522793879 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (2257810099 / 1000000000) (4522793879 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (13605498067 / 100000000000) (34215548777 / 250000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (59149594371 / 500000000000) (29743845293 / 250000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-29743845293 / 250000000000) (-59149594371 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (8539799749 / 500000000000) (9281503183 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (8539799749 / 500000000000) (9281503183 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1105825644933 / 500000000000) (1107724201047 / 500000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1107724201047 / 500000000000) (-1105825644933 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-549592200649 / 250000000000) (-4386176567 / 2000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-549592200649 / 250000000000) (-4386176567 / 2000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2200086008773 / 1000000000000) (551000185447 / 250000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1717206177 / 1000000000000) (682028643 / 62500000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (2599 / 204800) (1309 / 102400) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (2599 / 204800) ≤ m → m ≤ (1309 / 102400) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1309 / 102400) (2637 / 204800) m) :
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
  have hx0 : Bounds (1309 / 51200) (2637 / 102400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-2637 / 102400) (-1309 / 51200) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (99763 / 102400) (49891 / 51200) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (99763 / 102400) (49891 / 51200) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1309 / 25600) (2637 / 51200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-2637 / 51200) (-1309 / 25600) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (48563 / 51200) (24291 / 25600) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (48563 / 51200) (24291 / 25600) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(49891 / 51200)
  have hx9 : Bounds (101091 / 51200) (101091 / 51200) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49891 / 51200) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(49891 / 51200)
  have hx10 : Bounds (101091 / 51200) (101091 / 51200) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49891 / 51200) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (680281569 / 1000000000) (68028157 / 100000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (671585391521 / 500000000000) (1343170785017 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(49891 / 51200)
  have hx13 : Bounds (-49891 / 51200) (-49891 / 51200) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49891 / 51200) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1309 / 51200) (1309 / 51200) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(49891 / 51200)
  have hx15 : Bounds (1309 / 51200) (1309 / 51200) x15 := by
    exact hx14
  let x16 : ℝ := -(49891 / 51200)
  have hx16 : Bounds (-49891 / 51200) (-49891 / 51200) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49891 / 51200) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1309 / 51200) (1309 / 51200) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(49891 / 51200)
  have hx18 : Bounds (1309 / 51200) (1309 / 51200) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-229154753 / 62500000) (-1833238021 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-1874772323 / 20000000000) (-18747723199 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (312358041723 / 250000000000) (624716084511 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (312358041723 / 500000000000) (624716084511 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (312358041723 / 500000000000) (624716084511 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-624716084511 / 1000000000000) (-312358041723 / 500000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (68431095489 / 1000000000000) (34215548777 / 500000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (68431095489 / 1000000000000) (34215548777 / 500000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (49891 / 51200)
  have hx28 : Bounds (68431095489 / 1000000000000) (34215548777 / 500000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(99763 / 102400)
  have hx30 : Bounds (202163 / 102400) (202163 / 102400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99763 / 102400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(99763 / 102400)
  have hx31 : Bounds (202163 / 102400) (202163 / 102400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99763 / 102400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (68018759 / 100000000) (680187591 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (671429510533 / 500000000000) (1342859023041 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(99763 / 102400)
  have hx34 : Bounds (-99763 / 102400) (-99763 / 102400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99763 / 102400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (2637 / 102400) (2637 / 102400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(99763 / 102400)
  have hx36 : Bounds (2637 / 102400) (2637 / 102400) x36 := by
    exact hx35
  let x37 : ℝ := -(99763 / 102400)
  have hx37 : Bounds (-99763 / 102400) (-99763 / 102400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99763 / 102400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (2637 / 102400) (2637 / 102400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(99763 / 102400)
  have hx39 : Bounds (2637 / 102400) (2637 / 102400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-457405601 / 125000000) (-1829622401 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-94232700769 / 1000000000000) (-47116350307 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1248626320297 / 1000000000000) (1248626322427 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (156078290037 / 250000000000) (312156580607 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (156078290037 / 250000000000) (312156580607 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-312156580607 / 500000000000) (-156078290037 / 250000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (34417009393 / 500000000000) (17208505213 / 250000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (34417009393 / 500000000000) (17208505213 / 250000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (99763 / 102400)
  have hx49 : Bounds (34417009393 / 500000000000) (17208505213 / 250000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (68431095489 / 1000000000000) (17208505213 / 250000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(24291 / 25600)
  have hx52 : Bounds (49891 / 25600) (49891 / 25600) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24291 / 25600) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(24291 / 25600)
  have hx53 : Bounds (49891 / 25600) (49891 / 25600) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24291 / 25600) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (333624137 / 500000000) (26689931 / 40000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (650189133557 / 500000000000) (162547283633 / 125000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(24291 / 25600)
  have hx56 : Bounds (-24291 / 25600) (-24291 / 25600) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24291 / 25600) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1309 / 25600) (1309 / 25600) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(24291 / 25600)
  have hx58 : Bounds (1309 / 25600) (1309 / 25600) x58 := by
    exact hx57
  let x59 : ℝ := -(24291 / 25600)
  have hx59 : Bounds (-24291 / 25600) (-24291 / 25600) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24291 / 25600) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1309 / 25600) (1309 / 25600) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(24291 / 25600)
  have hx61 : Bounds (1309 / 25600) (1309 / 25600) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2973328867 / 1000000000) (-1486664431 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-76017333729 / 500000000000) (-152034667201 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (143542949957 / 125000000000) (1148343601863 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (143542949957 / 250000000000) (143542950233 / 250000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (143542949957 / 250000000000) (143542950233 / 250000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-143542950233 / 250000000000) (-143542949957 / 250000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (29743844767 / 250000000000) (29743845293 / 250000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (29743844767 / 250000000000) (29743845293 / 250000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (24291 / 25600)
  have hx71 : Bounds (29743844767 / 250000000000) (29743845293 / 250000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(48563 / 51200)
  have hx73 : Bounds (99763 / 51200) (99763 / 51200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48563 / 51200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(48563 / 51200)
  have hx74 : Bounds (99763 / 51200) (99763 / 51200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48563 / 51200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (667057841 / 1000000000) (333528921 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1299759597493 / 1000000000000) (1299759599443 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(48563 / 51200)
  have hx77 : Bounds (-48563 / 51200) (-48563 / 51200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48563 / 51200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2637 / 51200) (2637 / 51200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(48563 / 51200)
  have hx79 : Bounds (2637 / 51200) (2637 / 51200) x79 := by
    exact hx78
  let x80 : ℝ := -(48563 / 51200)
  have hx80 : Bounds (-48563 / 51200) (-48563 / 51200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48563 / 51200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2637 / 51200) (2637 / 51200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(48563 / 51200)
  have hx82 : Bounds (2637 / 51200) (2637 / 51200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2966097627 / 1000000000) (-1483048811 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-15276561411 / 100000000000) (-152765613851 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (1146993983383 / 1000000000000) (143374248199 / 125000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (573496991691 / 1000000000000) (143374248199 / 250000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (573496991691 / 1000000000000) (143374248199 / 250000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-143374248199 / 250000000000) (-573496991691 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (29912546801 / 250000000000) (119650189309 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (29912546801 / 250000000000) (119650189309 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (48563 / 51200)
  have hx92 : Bounds (29912546801 / 250000000000) (119650189309 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (29743844767 / 250000000000) (119650189309 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (29743844767 / 500000000000) (11965018931 / 200000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (29743844767 / 500000000000) (11965018931 / 200000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(12229 / 12500)
  have hx98 : Bounds (24729 / 12500) (24729 / 12500) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12229 / 12500) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(12229 / 12500)
  have hx99 : Bounds (24729 / 12500) (24729 / 12500) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12229 / 12500) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (682247999 / 1000000000) (85281 / 125000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1349704861381 / 1000000000000) (2108913849 / 1562500000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(12229 / 12500)
  have hx102 : Bounds (-12229 / 12500) (-12229 / 12500) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12229 / 12500) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (271 / 12500) (271 / 12500) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(12229 / 12500)
  have hx104 : Bounds (271 / 12500) (271 / 12500) x104 := by
    exact hx103
  let x105 : ℝ := -(12229 / 12500)
  have hx105 : Bounds (-12229 / 12500) (-12229 / 12500) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12229 / 12500) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (271 / 12500) (271 / 12500) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(12229 / 12500)
  have hx107 : Bounds (271 / 12500) (271 / 12500) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-766273021 / 200000000) (-3831365099 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-83063995477 / 1000000000000) (-41531997673 / 500000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (79165054119 / 62500000000) (633320434007 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (79165054119 / 125000000000) (633320434007 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (79165054119 / 125000000000) (633320434007 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-633320434007 / 1000000000000) (-79165054119 / 125000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (59826745993 / 1000000000000) (3739171753 / 62500000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (59826745993 / 1000000000000) (3739171753 / 62500000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (12229 / 12500)
  have hx117 : Bounds (59826745993 / 1000000000000) (3739171753 / 62500000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(978471 / 1000000)
  have hx119 : Bounds (1978471 / 1000000) (1978471 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978471 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(978471 / 1000000)
  have hx120 : Bounds (1978471 / 1000000) (1978471 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978471 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (170581081 / 250000000) (27292973 / 40000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (337489721907 / 250000000000) (168744861201 / 125000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(978471 / 1000000)
  have hx123 : Bounds (-978471 / 1000000) (-978471 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978471 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (21529 / 1000000) (21529 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(978471 / 1000000)
  have hx125 : Bounds (21529 / 1000000) (21529 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(978471 / 1000000)
  have hx126 : Bounds (-978471 / 1000000) (-978471 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978471 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (21529 / 1000000) (21529 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(978471 / 1000000)
  have hx128 : Bounds (21529 / 1000000) (21529 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1919177209 / 500000000) (-959588603 / 250000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-41317966133 / 500000000000) (-16527186427 / 200000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (633661477681 / 500000000000) (1267322957473 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (633661477681 / 1000000000000) (633661478737 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (633661477681 / 1000000000000) (633661478737 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-633661478737 / 1000000000000) (-633661477681 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (59485701263 / 1000000000000) (59485703319 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (59485701263 / 1000000000000) (59485703319 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (978471 / 1000000)
  have hx138 : Bounds (59485701263 / 1000000000000) (59485703319 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (12229 / 12500) (978471 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (978471 / 1000000) ≤ (59485703319 / 1000000000000) := hx138.2
      have h2 : (29743844767 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (11965018931 / 200000000000) := hx96.2
      have h2 : (59826745993 / 1000000000000) ≤ biasE (12229 / 12500) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1026237197089 / 1000000000000) (102643264537 / 100000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (7631059971 / 125000000000) (61406430167 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (7631059971 / 125000000000) (61406430167 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(244553 / 250000)
  have hx143 : Bounds (494553 / 250000) (494553 / 250000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244553 / 250000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(244553 / 250000)
  have hx144 : Bounds (494553 / 250000) (494553 / 250000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244553 / 250000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (341096703 / 500000000) (682193407 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (134952318207 / 100000000000) (1349523184049 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(244553 / 250000)
  have hx147 : Bounds (-244553 / 250000) (-244553 / 250000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244553 / 250000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (5447 / 250000) (5447 / 250000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(244553 / 250000)
  have hx149 : Bounds (5447 / 250000) (5447 / 250000) x149 := by
    exact hx148
  let x150 : ℝ := -(244553 / 250000)
  have hx150 : Bounds (-244553 / 250000) (-244553 / 250000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244553 / 250000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (5447 / 250000) (5447 / 250000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(244553 / 250000)
  have hx152 : Bounds (5447 / 250000) (5447 / 250000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-1913197961 / 500000000) (-956598979 / 250000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-83369514349 / 1000000000000) (-83369514217 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1266153667721 / 1000000000000) (158269208729 / 125000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (31653841693 / 50000000000) (158269208729 / 250000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (31653841693 / 50000000000) (158269208729 / 250000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-158269208729 / 250000000000) (-31653841693 / 50000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (15017586271 / 250000000000) (3003517357 / 50000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (15017586271 / 250000000000) (3003517357 / 50000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (244553 / 250000)
  have hx162 : Bounds (15017586271 / 250000000000) (3003517357 / 50000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(244591 / 250000)
  have hx164 : Bounds (494591 / 250000) (494591 / 250000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244591 / 250000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(244591 / 250000)
  have hx165 : Bounds (494591 / 250000) (494591 / 250000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244591 / 250000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (4264189 / 6250000) (682270241 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1349778881087 / 1000000000000) (674889441533 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(244591 / 250000)
  have hx168 : Bounds (-244591 / 250000) (-244591 / 250000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244591 / 250000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (5409 / 250000) (5409 / 250000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(244591 / 250000)
  have hx170 : Bounds (5409 / 250000) (5409 / 250000) x170 := by
    exact hx169
  let x171 : ℝ := -(244591 / 250000)
  have hx171 : Bounds (-244591 / 250000) (-244591 / 250000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244591 / 250000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (5409 / 250000) (5409 / 250000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(244591 / 250000)
  have hx173 : Bounds (5409 / 250000) (5409 / 250000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-239587293 / 62500000) (-1916698341 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-41469685371 / 500000000000) (-82939370611 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (253367902069 / 200000000000) (253367902491 / 200000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (158354938793 / 250000000000) (158354939057 / 250000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (158354938793 / 250000000000) (158354939057 / 250000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-158354939057 / 250000000000) (-158354938793 / 250000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (14931855943 / 250000000000) (14931856457 / 250000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (14931855943 / 250000000000) (14931856457 / 250000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (244591 / 250000)
  have hx183 : Bounds (14931855943 / 250000000000) (14931856457 / 250000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(244553 / 250000)
  have hx184 : Bounds (5971835549 / 100000000000) (60068506867 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((244553 / 250000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(244591 / 250000)
  have hx185 : Bounds (59727634859 / 1000000000000) (15019460161 / 250000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((244591 / 250000) : ℝ)) <;> norm_num
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
  have hc : Bounds (244553 / 250000) (244591 / 250000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (244553 / 250000) ≤ (60068506867 / 1000000000000) := hx184.2
      have h2 : (15017586271 / 250000000000) ≤ biasE (244553 / 250000) := hx162.1
      linarith
    · have h1 : biasE (244591 / 250000) ≤ (14931856457 / 250000000000) := hx183.2
      have h2 : (59727634859 / 1000000000000) ≤ x141 * (244591 / 250000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (24729 / 12500) (1978471 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-978471 / 1000000) (-12229 / 12500) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (21529 / 1000000) (271 / 12500) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (21529 / 1000000) (271 / 12500) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (11531365313653 / 250000000000) (11612243950021 / 250000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (11406365313653 / 125000000000) (11487243950021 / 125000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (11406365313653 / 125000000000) (11487243950021 / 125000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (2256806549 / 500000000) (4520678743 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (2256806549 / 1000000000) (4520678743 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (2256806549 / 1000000000) (4520678743 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (494553 / 250000) (494591 / 250000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-244591 / 250000) (-244553 / 250000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (5409 / 250000) (5447 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (5409 / 250000) (5447 / 250000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (45896823939783 / 1000000000000) (9243852837863 / 200000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (45396823939783 / 500000000000) (9143852837863 / 100000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (45396823939783 / 500000000000) (9143852837863 / 100000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (2254294661 / 500000000) (4515666929 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (2254294661 / 1000000000) (4515666929 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (2254294661 / 1000000000) (4515666929 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (68431095489 / 500000000000) (17208505213 / 125000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (29743844767 / 250000000000) (11965018931 / 100000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-11965018931 / 100000000000) (-29743844767 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (4303000417 / 250000000000) (4673165659 / 250000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (4303000417 / 250000000000) (4673165659 / 250000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2207878983017 / 1000000000000) (2211676525171 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2211676525171 / 1000000000000) (-2207878983017 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2194464523503 / 1000000000000) (-2189186320381 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2194464523503 / 1000000000000) (-2189186320381 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2196242170559 / 1000000000000) (1100054388451 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (111102941 / 62500000000) (10922456521 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1309 / 102400) (2637 / 204800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1309 / 102400) ≤ m → m ≤ (2637 / 204800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (2637 / 204800) (83 / 6400) m) :
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
  have hx0 : Bounds (2637 / 102400) (83 / 3200) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-83 / 3200) (-2637 / 102400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (3117 / 3200) (99763 / 102400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (3117 / 3200) (99763 / 102400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (2637 / 51200) (83 / 1600) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-83 / 1600) (-2637 / 51200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1517 / 1600) (48563 / 51200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (1517 / 1600) (48563 / 51200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(99763 / 102400)
  have hx9 : Bounds (202163 / 102400) (202163 / 102400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99763 / 102400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(99763 / 102400)
  have hx10 : Bounds (202163 / 102400) (202163 / 102400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99763 / 102400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (68018759 / 100000000) (680187591 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (671429510533 / 500000000000) (1342859023041 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(99763 / 102400)
  have hx13 : Bounds (-99763 / 102400) (-99763 / 102400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99763 / 102400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (2637 / 102400) (2637 / 102400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(99763 / 102400)
  have hx15 : Bounds (2637 / 102400) (2637 / 102400) x15 := by
    exact hx14
  let x16 : ℝ := -(99763 / 102400)
  have hx16 : Bounds (-99763 / 102400) (-99763 / 102400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99763 / 102400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (2637 / 102400) (2637 / 102400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(99763 / 102400)
  have hx18 : Bounds (2637 / 102400) (2637 / 102400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-457405601 / 125000000) (-1829622401 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-94232700769 / 1000000000000) (-47116350307 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1248626320297 / 1000000000000) (1248626322427 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (156078290037 / 250000000000) (312156580607 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (156078290037 / 250000000000) (312156580607 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-312156580607 / 500000000000) (-156078290037 / 250000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (34417009393 / 500000000000) (17208505213 / 250000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (34417009393 / 500000000000) (17208505213 / 250000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (99763 / 102400)
  have hx28 : Bounds (34417009393 / 500000000000) (17208505213 / 250000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(3117 / 3200)
  have hx30 : Bounds (6317 / 3200) (6317 / 3200) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3117 / 3200) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(3117 / 3200)
  have hx31 : Bounds (6317 / 3200) (6317 / 3200) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3117 / 3200) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (340046801 / 500000000) (680093603 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (671273638099 / 500000000000) (1342547278173 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(3117 / 3200)
  have hx34 : Bounds (-3117 / 3200) (-3117 / 3200) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3117 / 3200) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (83 / 3200) (83 / 3200) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(3117 / 3200)
  have hx36 : Bounds (83 / 3200) (83 / 3200) x36 := by
    exact hx35
  let x37 : ℝ := -(3117 / 3200)
  have hx37 : Bounds (-3117 / 3200) (-3117 / 3200) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3117 / 3200) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (83 / 3200) (83 / 3200) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(3117 / 3200)
  have hx39 : Bounds (83 / 3200) (83 / 3200) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-913016371 / 250000000) (-1826032739 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-23681362123 / 250000000000) (-18945089667 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (623910913853 / 500000000000) (623910914919 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (623910913853 / 1000000000000) (623910914919 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (623910913853 / 1000000000000) (623910914919 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-623910914919 / 1000000000000) (-623910913853 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (69236265081 / 1000000000000) (69236267147 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (69236265081 / 1000000000000) (69236267147 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (3117 / 3200)
  have hx49 : Bounds (69236265081 / 1000000000000) (69236267147 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (34417009393 / 500000000000) (69236267147 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(48563 / 51200)
  have hx52 : Bounds (99763 / 51200) (99763 / 51200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48563 / 51200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(48563 / 51200)
  have hx53 : Bounds (99763 / 51200) (99763 / 51200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48563 / 51200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (667057841 / 1000000000) (333528921 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1299759597493 / 1000000000000) (1299759599443 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(48563 / 51200)
  have hx56 : Bounds (-48563 / 51200) (-48563 / 51200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48563 / 51200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2637 / 51200) (2637 / 51200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(48563 / 51200)
  have hx58 : Bounds (2637 / 51200) (2637 / 51200) x58 := by
    exact hx57
  let x59 : ℝ := -(48563 / 51200)
  have hx59 : Bounds (-48563 / 51200) (-48563 / 51200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48563 / 51200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2637 / 51200) (2637 / 51200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(48563 / 51200)
  have hx61 : Bounds (2637 / 51200) (2637 / 51200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2966097627 / 1000000000) (-1483048811 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-15276561411 / 100000000000) (-152765613851 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1146993983383 / 1000000000000) (143374248199 / 125000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (573496991691 / 1000000000000) (143374248199 / 250000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (573496991691 / 1000000000000) (143374248199 / 250000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-143374248199 / 250000000000) (-573496991691 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (29912546801 / 250000000000) (119650189309 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (29912546801 / 250000000000) (119650189309 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (48563 / 51200)
  have hx71 : Bounds (29912546801 / 250000000000) (119650189309 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1517 / 1600)
  have hx73 : Bounds (3117 / 1600) (3117 / 1600) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1517 / 1600) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1517 / 1600)
  have hx74 : Bounds (3117 / 1600) (3117 / 1600) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1517 / 1600) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (666867371 / 1000000000) (166716843 / 250000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1299140997129 / 1000000000000) (649570499539 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1517 / 1600)
  have hx77 : Bounds (-1517 / 1600) (-1517 / 1600) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1517 / 1600) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (83 / 1600) (83 / 1600) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1517 / 1600)
  have hx79 : Bounds (83 / 1600) (83 / 1600) x79 := by
    exact hx78
  let x80 : ℝ := -(1517 / 1600)
  have hx80 : Bounds (-1517 / 1600) (-1517 / 1600) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1517 / 1600) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (83 / 1600) (83 / 1600) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1517 / 1600)
  have hx82 : Bounds (83 / 1600) (83 / 1600) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2958918303 / 1000000000) (-1479459149 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-153493886969 / 1000000000000) (-38373471677 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (14320588877 / 12500000000) (114564711237 / 100000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (14320588877 / 25000000000) (114564711237 / 200000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (14320588877 / 25000000000) (114564711237 / 200000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-114564711237 / 200000000000) (-14320588877 / 25000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (24064724763 / 200000000000) (376011331 / 3125000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (24064724763 / 200000000000) (376011331 / 3125000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1517 / 1600)
  have hx92 : Bounds (24064724763 / 200000000000) (376011331 / 3125000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (29912546801 / 250000000000) (376011331 / 3125000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (29912546801 / 500000000000) (376011331 / 6250000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (29912546801 / 500000000000) (376011331 / 6250000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(978171 / 1000000)
  have hx98 : Bounds (1978171 / 1000000) (1978171 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978171 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(978171 / 1000000)
  have hx99 : Bounds (1978171 / 1000000) (1978171 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978171 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (17054317 / 25000000) (682172681 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (168681776571 / 125000000000) (1349454214547 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(978171 / 1000000)
  have hx102 : Bounds (-978171 / 1000000) (-978171 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978171 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (21829 / 1000000) (21829 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(978171 / 1000000)
  have hx104 : Bounds (21829 / 1000000) (21829 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(978171 / 1000000)
  have hx105 : Bounds (-978171 / 1000000) (-978171 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978171 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (21829 / 1000000) (21829 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(978171 / 1000000)
  have hx107 : Bounds (21829 / 1000000) (21829 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-3824515921 / 1000000000) (-764903183 / 200000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-2087133951 / 25000000000) (-20871339477 / 250000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (2472595419 / 1953125000) (1265968856639 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (2472595419 / 3906250000) (3956152677 / 6250000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (2472595419 / 3906250000) (3956152677 / 6250000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-3956152677 / 6250000000) (-2472595419 / 3906250000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (188008599 / 3125000000) (7520344217 / 125000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (188008599 / 3125000000) (7520344217 / 125000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (978171 / 1000000)
  have hx117 : Bounds (188008599 / 3125000000) (7520344217 / 125000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(978321 / 1000000)
  have hx119 : Bounds (1978321 / 1000000) (1978321 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978321 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(978321 / 1000000)
  have hx120 : Bounds (1978321 / 1000000) (1978321 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978321 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (136449701 / 200000000) (341124253 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (67485327233 / 50000000000) (1349706546639 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(978321 / 1000000)
  have hx123 : Bounds (-978321 / 1000000) (-978321 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978321 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (21679 / 1000000) (21679 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(978321 / 1000000)
  have hx125 : Bounds (21679 / 1000000) (21679 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(978321 / 1000000)
  have hx126 : Bounds (-978321 / 1000000) (-978321 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978321 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (21679 / 1000000) (21679 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(978321 / 1000000)
  have hx128 : Bounds (21679 / 1000000) (21679 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-119731601 / 31250000) (-1915705613 / 500000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-83061164099 / 1000000000000) (-1297830687 / 15625000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1266645380561 / 1000000000000) (1266645382671 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (15833067257 / 25000000000) (79165336417 / 125000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (15833067257 / 25000000000) (79165336417 / 125000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-79165336417 / 125000000000) (-15833067257 / 25000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (7478061083 / 125000000000) (373903067 / 6250000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (7478061083 / 125000000000) (373903067 / 6250000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (978321 / 1000000)
  have hx138 : Bounds (7478061083 / 125000000000) (373903067 / 6250000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (978171 / 1000000) (978321 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (978321 / 1000000) ≤ (373903067 / 6250000000) := hx138.2
      have h2 : (29912546801 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (376011331 / 6250000000) := hx96.2
      have h2 : (188008599 / 3125000000) ≤ biasE (978171 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1026432645369 / 1000000000000) (1026628168111 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (12281285817 / 200000000000) (6176381183 / 100000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (12281285817 / 200000000000) (6176381183 / 100000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(978061 / 1000000)
  have hx143 : Bounds (1978061 / 1000000) (1978061 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978061 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(978061 / 1000000)
  have hx144 : Bounds (1978061 / 1000000) (1978061 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978061 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (682117071 / 1000000000) (42632317 / 62500000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1349269175579 / 1000000000000) (674634588779 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(978061 / 1000000)
  have hx147 : Bounds (-978061 / 1000000) (-978061 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978061 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (21939 / 1000000) (21939 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(978061 / 1000000)
  have hx149 : Bounds (21939 / 1000000) (21939 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(978061 / 1000000)
  have hx150 : Bounds (-978061 / 1000000) (-978061 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978061 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (21939 / 1000000) (21939 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(978061 / 1000000)
  have hx152 : Bounds (21939 / 1000000) (21939 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3819489407 / 1000000000) (-3819489401 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-83795778101 / 1000000000000) (-5237236123 / 62500000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (632736698739 / 500000000000) (126547339959 / 100000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (632736698739 / 1000000000000) (126547339959 / 200000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (632736698739 / 1000000000000) (126547339959 / 200000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-126547339959 / 200000000000) (-632736698739 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (12082096041 / 200000000000) (60410482261 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (12082096041 / 200000000000) (60410482261 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (978061 / 1000000)
  have hx162 : Bounds (12082096041 / 200000000000) (60410482261 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(978213 / 1000000)
  have hx164 : Bounds (1978213 / 1000000) (1978213 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978213 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(978213 / 1000000)
  have hx165 : Bounds (1978213 / 1000000) (1978213 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978213 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (682193911 / 1000000000) (85274239 / 125000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1349524863261 / 1000000000000) (33738121631 / 25000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(978213 / 1000000)
  have hx168 : Bounds (-978213 / 1000000) (-978213 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978213 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (21787 / 1000000) (21787 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(978213 / 1000000)
  have hx170 : Bounds (21787 / 1000000) (21787 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(978213 / 1000000)
  have hx171 : Bounds (-978213 / 1000000) (-978213 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978213 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (21787 / 1000000) (21787 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(978213 / 1000000)
  have hx173 : Bounds (21787 / 1000000) (21787 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-191322091 / 50000000) (-1913220907 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-83366687933 / 1000000000000) (-83366687801 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (39567442979 / 31250000000) (1266158177439 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (39567442979 / 62500000000) (7913488609 / 12500000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (39567442979 / 62500000000) (7913488609 / 12500000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-7913488609 / 12500000000) (-39567442979 / 62500000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (750851141 / 12500000000) (7508511667 / 125000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (750851141 / 12500000000) (7508511667 / 125000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (978213 / 1000000)
  have hx183 : Bounds (750851141 / 12500000000) (7508511667 / 125000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(978061 / 1000000)
  have hx184 : Bounds (60059233437 / 1000000000000) (60408775563 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((978061 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(978213 / 1000000)
  have hx185 : Bounds (30034283607 / 500000000000) (30209081831 / 500000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((978213 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (978061 / 1000000) (978213 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (978061 / 1000000) ≤ (60408775563 / 1000000000000) := hx184.2
      have h2 : (12082096041 / 200000000000) ≤ biasE (978061 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (978213 / 1000000) ≤ (7508511667 / 125000000000) := hx183.2
      have h2 : (30034283607 / 500000000000) ≤ x141 * (978213 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1978171 / 1000000) (1978321 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-978321 / 1000000) (-978171 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (21679 / 1000000) (21829 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (21679 / 1000000) (21829 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (45810618901461 / 1000000000000) (2882974306933 / 62500000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (45310618901461 / 500000000000) (2851724306933 / 31250000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (45310618901461 / 500000000000) (2851724306933 / 31250000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (901337719 / 200000000) (4513659737 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (901337719 / 400000000) (4513659737 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (901337719 / 400000000) (4513659737 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1978061 / 1000000) (1978213 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-978213 / 1000000) (-978061 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (21787 / 1000000) (21939 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (21787 / 1000000) (21939 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (45580928939331 / 1000000000000) (45898930554919 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (45080928939331 / 500000000000) (45398930554919 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (45080928939331 / 500000000000) (45398930554919 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (562700809 / 125000000) (1127158933 / 250000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (562700809 / 250000000) (1127158933 / 500000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (562700809 / 250000000) (1127158933 / 500000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (34417009393 / 250000000000) (69236267147 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (29912546801 / 250000000000) (376011331 / 3125000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-376011331 / 3125000000) (-29912546801 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (4336102913 / 250000000000) (1882234709 / 100000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (4336102913 / 250000000000) (1882234709 / 100000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2204156044829 / 1000000000000) (2207904053781 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2207904053781 / 1000000000000) (-2204156044829 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2190559642129 / 1000000000000) (-2185333697739 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2190559642129 / 1000000000000) (-2185333697739 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1096211513533 / 500000000000) (1098132388993 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1863384937 / 1000000000000) (10931080247 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (2637 / 204800) (83 / 6400) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (2637 / 204800) ≤ m → m ≤ (83 / 6400) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038

end


