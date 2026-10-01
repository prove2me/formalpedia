-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0259__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0259__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:33:32.535248+00:00
-- url     : https://prove2.me/theorems/439d5b79-10b7-418e-a031-f9ea6ef0186f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259 (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259 (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259 (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259 (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0259 (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0260, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0261, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0262, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0263, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0264).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0255Logs__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0262Logs__5

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0259
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3739 / 10240) (1871 / 5120) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (3739 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (3739 / 5120) (1871 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1871 / 2560) (-3739 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (689 / 2560) (1381 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (689 / 2560) (1381 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3739 / 2560) (1871 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1871 / 1280) (-3739 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (689 / 1280) (1381 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (689 / 1280) (1381 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1381 / 5120)
  have hx9 : Bounds (6501 / 5120) (6501 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1381 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1381 / 5120)
  have hx10 : Bounds (6501 / 5120) (6501 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1381 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (59700393 / 250000000) (238801573 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (60642539827 / 200000000000) (60642540081 / 200000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1381 / 5120)
  have hx13 : Bounds (-1381 / 5120) (-1381 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1381 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3739 / 5120) (3739 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1381 / 5120)
  have hx15 : Bounds (3739 / 5120) (3739 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(1381 / 5120)
  have hx16 : Bounds (-1381 / 5120) (-1381 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1381 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3739 / 5120) (3739 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1381 / 5120)
  have hx18 : Bounds (3739 / 5120) (3739 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-78584061 / 250000000) (-314336243 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-229551409437 / 1000000000000) (-114775704353 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (36830644849 / 500000000000) (73661291699 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (36830644849 / 1000000000000) (736612917 / 20000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (36830644849 / 1000000000000) (736612917 / 20000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-736612917 / 20000000000) (-36830644849 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (13126330683 / 20000000000) (656316536151 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (13126330683 / 20000000000) (656316536151 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1381 / 5120)
  have hx28 : Bounds (13126330683 / 20000000000) (656316536151 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(689 / 2560)
  have hx30 : Bounds (3249 / 2560) (3249 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(689 / 2560)
  have hx31 : Bounds (3249 / 2560) (3249 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (119169999 / 500000000) (238339999 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (37810871753 / 125000000000) (151243487647 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(689 / 2560)
  have hx34 : Bounds (-689 / 2560) (-689 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1871 / 2560) (1871 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(689 / 2560)
  have hx36 : Bounds (1871 / 2560) (1871 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(689 / 2560)
  have hx37 : Bounds (-689 / 2560) (-689 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1871 / 2560) (1871 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(689 / 2560)
  have hx39 : Bounds (1871 / 2560) (1871 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-78383553 / 250000000) (-313534211 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-14321838639 / 62500000000) (-57287354373 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (366687779 / 5000000000) (36668778901 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (366687779 / 10000000000) (36668778901 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (366687779 / 10000000000) (36668778901 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-36668778901 / 1000000000000) (-366687779 / 10000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (656478401099 / 1000000000000) (6564784031 / 10000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (656478401099 / 1000000000000) (6564784031 / 10000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (689 / 2560)
  have hx49 : Bounds (656478401099 / 1000000000000) (6564784031 / 10000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (13126330683 / 20000000000) (6564784031 / 10000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1381 / 2560)
  have hx52 : Bounds (3941 / 2560) (3941 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1381 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1381 / 2560)
  have hx53 : Bounds (3941 / 2560) (3941 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1381 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (431427239 / 1000000000) (10785681 / 25000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (83020251411 / 125000000000) (664162012829 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1381 / 2560)
  have hx56 : Bounds (-1381 / 2560) (-1381 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1381 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1179 / 2560) (1179 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1381 / 2560)
  have hx58 : Bounds (1179 / 2560) (1179 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(1381 / 2560)
  have hx59 : Bounds (-1381 / 2560) (-1381 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1381 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1179 / 2560) (1179 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1381 / 2560)
  have hx61 : Bounds (1179 / 2560) (1179 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-387670319 / 500000000) (-193835159 / 250000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-89270176973 / 250000000000) (-35708070697 / 100000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (76770325849 / 250000000000) (307081305859 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (76770325849 / 500000000000) (15354065293 / 100000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (76770325849 / 500000000000) (15354065293 / 100000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-15354065293 / 100000000000) (-76770325849 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (53960652707 / 100000000000) (269803264651 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (53960652707 / 100000000000) (269803264651 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1381 / 2560)
  have hx71 : Bounds (53960652707 / 100000000000) (269803264651 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(689 / 1280)
  have hx73 : Bounds (1969 / 1280) (1969 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(689 / 1280)
  have hx74 : Bounds (1969 / 1280) (1969 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (430665721 / 1000000000) (215332861 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (41405312727 / 62500000000) (662485005171 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(689 / 1280)
  have hx77 : Bounds (-689 / 1280) (-689 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (591 / 1280) (591 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(689 / 1280)
  have hx79 : Bounds (591 / 1280) (591 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(689 / 1280)
  have hx80 : Bounds (-689 / 1280) (-689 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (591 / 1280) (591 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(689 / 1280)
  have hx82 : Bounds (591 / 1280) (591 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-38639967 / 50000000) (-386399669 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-178407972633 / 500000000000) (-178407972171 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (152834529183 / 500000000000) (305669060829 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (152834529183 / 1000000000000) (30566906083 / 200000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (152834529183 / 1000000000000) (30566906083 / 200000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-30566906083 / 200000000000) (-152834529183 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (108062529917 / 200000000000) (540312651817 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (108062529917 / 200000000000) (540312651817 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (689 / 1280)
  have hx92 : Bounds (108062529917 / 200000000000) (540312651817 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (53960652707 / 100000000000) (540312651817 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (123275370707 / 100000000000) (1233459832817 / 1000000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (123275370707 / 200000000000) (616729916409 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (123275370707 / 200000000000) (616729916409 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(3087 / 8000)
  have hx100 : Bounds (11087 / 8000) (11087 / 8000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3087 / 8000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(3087 / 8000)
  have hx101 : Bounds (11087 / 8000) (11087 / 8000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3087 / 8000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (326331709 / 1000000000) (32633171 / 100000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (45225495721 / 100000000000) (452254958597 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(3087 / 8000)
  have hx104 : Bounds (-3087 / 8000) (-3087 / 8000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3087 / 8000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (4913 / 8000) (4913 / 8000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(3087 / 8000)
  have hx106 : Bounds (4913 / 8000) (4913 / 8000) x106 := by
    exact hx105
  let x107 : ℝ := -(3087 / 8000)
  have hx107 : Bounds (-3087 / 8000) (-3087 / 8000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3087 / 8000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (4913 / 8000) (4913 / 8000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(3087 / 8000)
  have hx109 : Bounds (4913 / 8000) (4913 / 8000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-487556789 / 1000000000) (-121889197 / 250000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-59884162609 / 200000000000) (-29942081243 / 100000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (30566828833 / 200000000000) (152834146167 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (38208536041 / 500000000000) (19104268271 / 250000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (38208536041 / 500000000000) (19104268271 / 250000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-19104268271 / 250000000000) (-38208536041 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (154182526729 / 250000000000) (308365054459 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (154182526729 / 250000000000) (308365054459 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (3087 / 8000)
  have hx119 : Bounds (154182526729 / 250000000000) (308365054459 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(193371 / 500000)
  have hx121 : Bounds (693371 / 500000) (693371 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193371 / 500000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(193371 / 500000)
  have hx122 : Bounds (693371 / 500000) (693371 / 500000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193371 / 500000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (326957111 / 1000000000) (40869639 / 125000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (226702579011 / 500000000000) (45340515941 / 100000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(193371 / 500000)
  have hx125 : Bounds (-193371 / 500000) (-193371 / 500000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193371 / 500000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (306629 / 500000) (306629 / 500000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(193371 / 500000)
  have hx127 : Bounds (306629 / 500000) (306629 / 500000) x127 := by
    exact hx126
  let x128 : ℝ := -(193371 / 500000)
  have hx128 : Bounds (-193371 / 500000) (-193371 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193371 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (306629 / 500000) (306629 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(193371 / 500000)
  have hx130 : Bounds (306629 / 500000) (306629 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-488969551 / 1000000000) (-9779391 / 20000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-74966122227 / 250000000000) (-299864488293 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (76770334557 / 500000000000) (153540671117 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (76770334557 / 1000000000000) (76770335559 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (76770334557 / 1000000000000) (76770335559 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-76770335559 / 1000000000000) (-76770334557 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (616376844441 / 1000000000000) (616376846443 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (616376844441 / 1000000000000) (616376846443 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (193371 / 500000)
  have hx140 : Bounds (616376844441 / 1000000000000) (616376846443 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (3087 / 8000) (193371 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (193371 / 500000) ≤ (616376846443 / 1000000000000) := hx140.2
      have h2 : (123275370707 / 200000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (616729916409 / 1000000000000) := hx98.2
      have h2 : (154182526729 / 250000000000) ≤ biasE (3087 / 8000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (231716147719 / 62500000000) (1857764876633 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (571297880177 / 250000000000) (2291478354147 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (571297880177 / 250000000000) (2291478354147 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(71143 / 250000)
  have hx145 : Bounds (321143 / 250000) (321143 / 250000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((71143 / 250000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(71143 / 250000)
  have hx146 : Bounds (321143 / 250000) (321143 / 250000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((71143 / 250000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (62606397 / 250000000) (250425589 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (80422424607 / 250000000000) (321689699713 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(71143 / 250000)
  have hx149 : Bounds (-71143 / 250000) (-71143 / 250000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((71143 / 250000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (178857 / 250000) (178857 / 250000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(71143 / 250000)
  have hx151 : Bounds (178857 / 250000) (178857 / 250000) x151 := by
    exact hx150
  let x152 : ℝ := -(71143 / 250000)
  have hx152 : Bounds (-71143 / 250000) (-71143 / 250000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((71143 / 250000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (178857 / 250000) (178857 / 250000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(71143 / 250000)
  have hx154 : Bounds (178857 / 250000) (178857 / 250000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-167437157 / 500000000) (-334874313 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-239578460717 / 1000000000000) (-11978923 / 50000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (82111237711 / 1000000000000) (82111239713 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (8211123771 / 200000000000) (41055619857 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (8211123771 / 200000000000) (41055619857 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-41055619857 / 1000000000000) (-8211123771 / 200000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (652091560143 / 1000000000000) (130418312429 / 200000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (652091560143 / 1000000000000) (130418312429 / 200000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (71143 / 250000)
  have hx164 : Bounds (652091560143 / 1000000000000) (130418312429 / 200000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(285267 / 1000000)
  have hx166 : Bounds (1285267 / 1000000) (1285267 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((285267 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(285267 / 1000000)
  have hx167 : Bounds (1285267 / 1000000) (1285267 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((285267 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (125483239 / 500000000) (250966479 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (322558932279 / 1000000000000) (64511786713 / 200000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(285267 / 1000000)
  have hx170 : Bounds (-285267 / 1000000) (-285267 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((285267 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (714733 / 1000000) (714733 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(285267 / 1000000)
  have hx172 : Bounds (714733 / 1000000) (714733 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(285267 / 1000000)
  have hx173 : Bounds (-285267 / 1000000) (-285267 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((285267 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (714733 / 1000000) (714733 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(285267 / 1000000)
  have hx175 : Bounds (714733 / 1000000) (714733 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-335846233 / 1000000000) (-41980779 / 125000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-240040385651 / 1000000000000) (-30005048117 / 125000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (20629636657 / 250000000000) (82518548629 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (20629636657 / 500000000000) (8251854863 / 200000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (20629636657 / 500000000000) (8251854863 / 200000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-8251854863 / 200000000000) (-20629636657 / 500000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (130377581137 / 200000000000) (325943953843 / 500000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (130377581137 / 200000000000) (325943953843 / 500000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (285267 / 1000000)
  have hx185 : Bounds (130377581137 / 200000000000) (325943953843 / 500000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(71143 / 250000)
  have hx186 : Bounds (65030152143 / 100000000000) (652090578197 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((71143 / 250000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(285267 / 1000000)
  have hx187 : Bounds (651889729537 / 1000000000000) (653683155653 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((285267 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (71143 / 250000) (285267 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (71143 / 250000) ≤ (652090578197 / 1000000000000) := hx186.2
      have h2 : (652091560143 / 1000000000000) ≤ biasE (71143 / 250000) := hx164.1
      linarith
    · have h1 : biasE (285267 / 1000000) ≤ (325943953843 / 500000000000) := hx185.2
      have h2 : (651889729537 / 1000000000000) ≤ x143 * (285267 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (11087 / 8000) (693371 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-193371 / 500000) (-3087 / 8000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (306629 / 500000) (4913 / 8000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (306629 / 500000) (4913 / 8000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1628332994097 / 1000000000000) (815317533567 / 500000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (1128332994097 / 500000000000) (565317533567 / 250000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (1128332994097 / 500000000000) (565317533567 / 250000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (813888497 / 1000000000) (815926663 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (813888497 / 2000000000) (815926663 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (813888497 / 2000000000) (815926663 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (321143 / 250000) (1285267 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-285267 / 1000000) (-71143 / 250000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (714733 / 1000000) (178857 / 250000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (714733 / 1000000) (178857 / 250000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (13977646947 / 10000000000) (699561934317 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (8977646947 / 5000000000) (449561934317 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (8977646947 / 5000000000) (449561934317 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (292649951 / 500000000) (73351589 / 125000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (292649951 / 1000000000) (73351589 / 250000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (292649951 / 1000000000) (73351589 / 250000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (13126330683 / 10000000000) (6564784031 / 5000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (123275370707 / 100000000000) (616729916409 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-616729916409 / 500000000000) (-123275370707 / 100000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (39586617741 / 500000000000) (8020309913 / 100000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (39586617741 / 500000000000) (8020309913 / 100000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (157029611889 / 1000000000000) (157776554751 / 1000000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-157776554751 / 1000000000000) (-157029611889 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-78603319269 / 1000000000000) (-76826512759 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-78603319269 / 1000000000000) (-76826512759 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (39381995359 / 500000000000) (3956974391 / 50000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (160671449 / 1000000000000) (2312975061 / 1000000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3739 / 10240) (1871 / 5120) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3739 / 10240) ≤ m → m ≤ (1871 / 5120) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0259

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0260
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1871 / 5120) (749 / 2048) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (1871 / 5120) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1871 / 2560) (749 / 1024) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-749 / 1024) (-1871 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (275 / 1024) (689 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (275 / 1024) (689 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1871 / 1280) (749 / 512) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-749 / 512) (-1871 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (275 / 512) (689 / 1280) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (275 / 512) (689 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(689 / 2560)
  have hx9 : Bounds (3249 / 2560) (3249 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(689 / 2560)
  have hx10 : Bounds (3249 / 2560) (3249 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (119169999 / 500000000) (238339999 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (37810871753 / 125000000000) (151243487647 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(689 / 2560)
  have hx13 : Bounds (-689 / 2560) (-689 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1871 / 2560) (1871 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(689 / 2560)
  have hx15 : Bounds (1871 / 2560) (1871 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(689 / 2560)
  have hx16 : Bounds (-689 / 2560) (-689 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1871 / 2560) (1871 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(689 / 2560)
  have hx18 : Bounds (1871 / 2560) (1871 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-78383553 / 250000000) (-313534211 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-14321838639 / 62500000000) (-57287354373 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (366687779 / 5000000000) (36668778901 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (366687779 / 10000000000) (36668778901 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (366687779 / 10000000000) (36668778901 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-36668778901 / 1000000000000) (-366687779 / 10000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (656478401099 / 1000000000000) (6564784031 / 10000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (656478401099 / 1000000000000) (6564784031 / 10000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (689 / 2560)
  have hx28 : Bounds (656478401099 / 1000000000000) (6564784031 / 10000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(275 / 1024)
  have hx30 : Bounds (1299 / 1024) (1299 / 1024) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 1024) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(275 / 1024)
  have hx31 : Bounds (1299 / 1024) (1299 / 1024) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 1024) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (237878211 / 1000000000) (59469553 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (150880759809 / 500000000000) (301761520887 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(275 / 1024)
  have hx34 : Bounds (-275 / 1024) (-275 / 1024) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 1024) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (749 / 1024) (749 / 1024) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(275 / 1024)
  have hx36 : Bounds (749 / 1024) (749 / 1024) x36 := by
    exact hx35
  let x37 : ℝ := -(275 / 1024)
  have hx37 : Bounds (-275 / 1024) (-275 / 1024) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 1024) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (749 / 1024) (749 / 1024) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(275 / 1024)
  have hx39 : Bounds (749 / 1024) (749 / 1024) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-312732823 / 1000000000) (-156366411 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-228746957449 / 1000000000000) (-57186739179 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (73014562169 / 1000000000000) (73014564171 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (9126820271 / 250000000000) (18253641043 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (9126820271 / 250000000000) (18253641043 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-18253641043 / 500000000000) (-9126820271 / 250000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (328319948957 / 500000000000) (164159974979 / 250000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (328319948957 / 500000000000) (164159974979 / 250000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (275 / 1024)
  have hx49 : Bounds (328319948957 / 500000000000) (164159974979 / 250000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (656478401099 / 1000000000000) (164159974979 / 250000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(689 / 1280)
  have hx52 : Bounds (1969 / 1280) (1969 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(689 / 1280)
  have hx53 : Bounds (1969 / 1280) (1969 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((689 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (430665721 / 1000000000) (215332861 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (41405312727 / 62500000000) (662485005171 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(689 / 1280)
  have hx56 : Bounds (-689 / 1280) (-689 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (591 / 1280) (591 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(689 / 1280)
  have hx58 : Bounds (591 / 1280) (591 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(689 / 1280)
  have hx59 : Bounds (-689 / 1280) (-689 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((689 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (591 / 1280) (591 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(689 / 1280)
  have hx61 : Bounds (591 / 1280) (591 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-38639967 / 50000000) (-386399669 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-178407972633 / 500000000000) (-178407972171 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (152834529183 / 500000000000) (305669060829 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (152834529183 / 1000000000000) (30566906083 / 200000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (152834529183 / 1000000000000) (30566906083 / 200000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-30566906083 / 200000000000) (-152834529183 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (108062529917 / 200000000000) (540312651817 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (108062529917 / 200000000000) (540312651817 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (689 / 1280)
  have hx71 : Bounds (108062529917 / 200000000000) (540312651817 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(275 / 512)
  have hx73 : Bounds (787 / 512) (787 / 512) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 512) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(275 / 512)
  have hx74 : Bounds (787 / 512) (787 / 512) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 512) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (429903623 / 1000000000) (53737953 / 125000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (660808889259 / 1000000000000) (660808890797 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(275 / 512)
  have hx77 : Bounds (-275 / 512) (-275 / 512) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 512) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (237 / 512) (237 / 512) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(275 / 512)
  have hx79 : Bounds (237 / 512) (237 / 512) x79 := by
    exact hx78
  let x80 : ℝ := -(275 / 512)
  have hx80 : Bounds (-275 / 512) (-275 / 512) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 512) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (237 / 512) (237 / 512) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(275 / 512)
  have hx82 : Bounds (237 / 512) (237 / 512) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-154052897 / 200000000) (-770264483 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-356548208877 / 1000000000000) (-356548207951 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (152130340191 / 500000000000) (152130341423 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (152130340191 / 1000000000000) (152130341423 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (152130340191 / 1000000000000) (152130341423 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-152130341423 / 1000000000000) (-152130340191 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (541016838577 / 1000000000000) (541016840809 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (541016838577 / 1000000000000) (541016840809 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (275 / 512)
  have hx92 : Bounds (541016838577 / 1000000000000) (541016840809 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (108062529917 / 200000000000) (541016840809 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (246691965917 / 200000000000) (1234164021809 / 1000000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (77091239349 / 125000000000) (123416402181 / 200000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (77091239349 / 125000000000) (123416402181 / 200000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(385009 / 1000000)
  have hx100 : Bounds (1385009 / 1000000) (1385009 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((385009 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(385009 / 1000000)
  have hx101 : Bounds (1385009 / 1000000) (1385009 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((385009 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (325706637 / 1000000000) (162853319 / 500000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (112776655901 / 250000000000) (45110662499 / 100000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(385009 / 1000000)
  have hx104 : Bounds (-385009 / 1000000) (-385009 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((385009 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (614991 / 1000000) (614991 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(385009 / 1000000)
  have hx106 : Bounds (614991 / 1000000) (614991 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(385009 / 1000000)
  have hx107 : Bounds (-385009 / 1000000) (-385009 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((385009 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (614991 / 1000000) (614991 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(385009 / 1000000)
  have hx109 : Bounds (614991 / 1000000) (614991 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-243073823 / 500000000) (-97229529 / 200000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-149488213481 / 500000000000) (-149488213173 / 500000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (76065098321 / 500000000000) (38032549661 / 250000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (76065098321 / 1000000000000) (38032549661 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (76065098321 / 1000000000000) (38032549661 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-38032549661 / 500000000000) (-76065098321 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (308541040339 / 500000000000) (617082082679 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (308541040339 / 500000000000) (617082082679 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (385009 / 1000000)
  have hx119 : Bounds (308541040339 / 500000000000) (617082082679 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(96469 / 250000)
  have hx121 : Bounds (346469 / 250000) (346469 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96469 / 250000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(96469 / 250000)
  have hx122 : Bounds (346469 / 250000) (346469 / 250000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96469 / 250000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (32633243 / 100000000) (326332431 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (226128141379 / 500000000000) (90451256829 / 200000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(96469 / 250000)
  have hx125 : Bounds (-96469 / 250000) (-96469 / 250000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96469 / 250000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (153531 / 250000) (153531 / 250000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(96469 / 250000)
  have hx127 : Bounds (153531 / 250000) (153531 / 250000) x127 := by
    exact hx126
  let x128 : ℝ := -(96469 / 250000)
  have hx128 : Bounds (-96469 / 250000) (-96469 / 250000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96469 / 250000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (153531 / 250000) (153531 / 250000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(96469 / 250000)
  have hx130 : Bounds (153531 / 250000) (153531 / 250000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-487558417 / 1000000000) (-30472401 / 62500000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-149710662641 / 500000000000) (-299421324667 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (38208739369 / 250000000000) (76417479739 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (38208739369 / 500000000000) (76417479739 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (38208739369 / 500000000000) (76417479739 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-76417479739 / 1000000000000) (-38208739369 / 500000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (616729700261 / 1000000000000) (308364851131 / 500000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (616729700261 / 1000000000000) (308364851131 / 500000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (96469 / 250000)
  have hx140 : Bounds (616729700261 / 1000000000000) (308364851131 / 500000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (385009 / 1000000) (96469 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (96469 / 250000) ≤ (308364851131 / 500000000000) := hx140.2
      have h2 : (77091239349 / 125000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (123416402181 / 200000000000) := hx98.2
      have h2 : (308541040339 / 500000000000) ≤ biasE (385009 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (743105950653 / 200000000000) (3723636363637 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1145739174069 / 500000000000) (2297789015153 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1145739174069 / 500000000000) (2297789015153 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(283879 / 1000000)
  have hx145 : Bounds (1283879 / 1000000) (1283879 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((283879 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(283879 / 1000000)
  have hx146 : Bounds (1283879 / 1000000) (1283879 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((283879 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (62471491 / 250000000) (49977193 / 200000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (160411670787 / 500000000000) (320823342859 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(283879 / 1000000)
  have hx149 : Bounds (-283879 / 1000000) (-283879 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((283879 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (716121 / 1000000) (716121 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(283879 / 1000000)
  have hx151 : Bounds (716121 / 1000000) (716121 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(283879 / 1000000)
  have hx152 : Bounds (-283879 / 1000000) (-283879 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((283879 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (716121 / 1000000) (716121 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(283879 / 1000000)
  have hx154 : Bounds (716121 / 1000000) (716121 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-83476533 / 250000000) (-333906131 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-119558596577 / 500000000000) (-239117192437 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (4085307421 / 50000000000) (40853075211 / 500000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (4085307421 / 100000000000) (40853075211 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (4085307421 / 100000000000) (40853075211 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-40853075211 / 1000000000000) (-4085307421 / 100000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (652294104789 / 1000000000000) (65229410679 / 100000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (652294104789 / 1000000000000) (65229410679 / 100000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (283879 / 1000000)
  have hx164 : Bounds (652294104789 / 1000000000000) (65229410679 / 100000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(284573 / 1000000)
  have hx166 : Bounds (1284573 / 1000000) (1284573 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((284573 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(284573 / 1000000)
  have hx167 : Bounds (1284573 / 1000000) (1284573 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((284573 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (250426367 / 1000000000) (489114 / 1953125) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (10052842173 / 31250000000) (321690950821 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(284573 / 1000000)
  have hx170 : Bounds (-284573 / 1000000) (-284573 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((284573 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (715427 / 1000000) (715427 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(284573 / 1000000)
  have hx172 : Bounds (715427 / 1000000) (715427 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(284573 / 1000000)
  have hx173 : Bounds (-284573 / 1000000) (-284573 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((284573 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (715427 / 1000000) (715427 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(284573 / 1000000)
  have hx175 : Bounds (715427 / 1000000) (715427 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-5232433 / 15625000) (-334875711 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-23957912601 / 100000000000) (-239579125293 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (41055911763 / 500000000000) (10263978191 / 125000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (41055911763 / 1000000000000) (10263978191 / 250000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (41055911763 / 1000000000000) (10263978191 / 250000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-10263978191 / 250000000000) (-41055911763 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (163022816809 / 250000000000) (652091269237 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (163022816809 / 250000000000) (652091269237 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (284573 / 1000000)
  have hx185 : Bounds (163022816809 / 250000000000) (652091269237 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(283879 / 1000000)
  have hx186 : Bounds (650502581991 / 1000000000000) (652294047833 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((283879 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(284573 / 1000000)
  have hx187 : Bounds (163023216991 / 250000000000) (65388871341 / 100000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((284573 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (283879 / 1000000) (284573 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (283879 / 1000000) ≤ (652294047833 / 1000000000000) := hx186.2
      have h2 : (652294104789 / 1000000000000) ≤ biasE (283879 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (284573 / 1000000) ≤ (652091269237 / 1000000000000) := hx185.2
      have h2 : (163023216991 / 250000000000) ≤ x143 * (284573 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1385009 / 1000000) (346469 / 250000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-96469 / 250000) (-385009 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (153531 / 250000) (614991 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (153531 / 250000) (614991 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (162604005587 / 100000000000) (162833564557 / 100000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (112604005587 / 50000000000) (112833564557 / 50000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (112604005587 / 50000000000) (112833564557 / 50000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (405927141 / 500000000) (25434089 / 31250000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (405927141 / 1000000000) (25434089 / 62500000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (405927141 / 1000000000) (25434089 / 62500000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1283879 / 1000000) (1284573 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-284573 / 1000000) (-283879 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (715427 / 1000000) (716121 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (715427 / 1000000) (716121 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (279282411771 / 200000000000) (27955332969 / 20000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (179282411771 / 100000000000) (17955332969 / 10000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (179282411771 / 100000000000) (17955332969 / 10000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (116758419 / 200000000) (1829069 / 3125000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (116758419 / 400000000) (1829069 / 6250000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (116758419 / 400000000) (1829069 / 6250000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (656478401099 / 500000000000) (164159974979 / 125000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (77091239349 / 62500000000) (123416402181 / 100000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-123416402181 / 100000000000) (-77091239349 / 62500000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (19698195097 / 250000000000) (9977496281 / 125000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (19698195097 / 250000000000) (9977496281 / 125000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (156285602629 / 1000000000000) (9814404527 / 62500000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-9814404527 / 62500000000) (-156285602629 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-19559423011 / 250000000000) (-76465632381 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-19559423011 / 250000000000) (-76465632381 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (39195025909 / 500000000000) (78764283813 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (76179887 / 500000000000) (287331429 / 125000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1871 / 5120) (749 / 2048) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1871 / 5120) ≤ m → m ≤ (749 / 2048) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0260

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0261
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (749 / 2048) (937 / 2560) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (749 / 2048) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (749 / 1024) (937 / 1280) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-937 / 1280) (-749 / 1024) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (343 / 1280) (275 / 1024) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (343 / 1280) (275 / 1024) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (749 / 512) (937 / 640) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-937 / 640) (-749 / 512) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (343 / 640) (275 / 512) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (343 / 640) (275 / 512) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(275 / 1024)
  have hx9 : Bounds (1299 / 1024) (1299 / 1024) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 1024) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(275 / 1024)
  have hx10 : Bounds (1299 / 1024) (1299 / 1024) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 1024) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (237878211 / 1000000000) (59469553 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (150880759809 / 500000000000) (301761520887 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(275 / 1024)
  have hx13 : Bounds (-275 / 1024) (-275 / 1024) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 1024) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (749 / 1024) (749 / 1024) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(275 / 1024)
  have hx15 : Bounds (749 / 1024) (749 / 1024) x15 := by
    exact hx14
  let x16 : ℝ := -(275 / 1024)
  have hx16 : Bounds (-275 / 1024) (-275 / 1024) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 1024) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (749 / 1024) (749 / 1024) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(275 / 1024)
  have hx18 : Bounds (749 / 1024) (749 / 1024) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-312732823 / 1000000000) (-156366411 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-228746957449 / 1000000000000) (-57186739179 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (73014562169 / 1000000000000) (73014564171 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (9126820271 / 250000000000) (18253641043 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (9126820271 / 250000000000) (18253641043 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-18253641043 / 500000000000) (-9126820271 / 250000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (328319948957 / 500000000000) (164159974979 / 250000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (328319948957 / 500000000000) (164159974979 / 250000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (275 / 1024)
  have hx28 : Bounds (328319948957 / 500000000000) (164159974979 / 250000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(343 / 1280)
  have hx30 : Bounds (1623 / 1280) (1623 / 1280) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 1280) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(343 / 1280)
  have hx31 : Bounds (1623 / 1280) (1623 / 1280) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 1280) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (23741621 / 100000000) (237416211 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (301036335023 / 1000000000000) (75259084073 / 250000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(343 / 1280)
  have hx34 : Bounds (-343 / 1280) (-343 / 1280) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 1280) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (937 / 1280) (937 / 1280) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(343 / 1280)
  have hx36 : Bounds (937 / 1280) (937 / 1280) x36 := by
    exact hx35
  let x37 : ℝ := -(343 / 1280)
  have hx37 : Bounds (-343 / 1280) (-343 / 1280) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 1280) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (937 / 1280) (937 / 1280) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(343 / 1280)
  have hx39 : Bounds (937 / 1280) (937 / 1280) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-12477283 / 40000000) (-155966037 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-114172013389 / 500000000000) (-45668805209 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (14538461649 / 200000000000) (72692310247 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (18173077061 / 500000000000) (9086538781 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (18173077061 / 500000000000) (9086538781 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-9086538781 / 250000000000) (-18173077061 / 500000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (164200256219 / 250000000000) (328400513439 / 500000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (164200256219 / 250000000000) (328400513439 / 500000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (343 / 1280)
  have hx49 : Bounds (164200256219 / 250000000000) (328400513439 / 500000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (328319948957 / 500000000000) (328400513439 / 500000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(275 / 512)
  have hx52 : Bounds (787 / 512) (787 / 512) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 512) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(275 / 512)
  have hx53 : Bounds (787 / 512) (787 / 512) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((275 / 512) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (429903623 / 1000000000) (53737953 / 125000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (660808889259 / 1000000000000) (660808890797 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(275 / 512)
  have hx56 : Bounds (-275 / 512) (-275 / 512) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 512) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (237 / 512) (237 / 512) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(275 / 512)
  have hx58 : Bounds (237 / 512) (237 / 512) x58 := by
    exact hx57
  let x59 : ℝ := -(275 / 512)
  have hx59 : Bounds (-275 / 512) (-275 / 512) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((275 / 512) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (237 / 512) (237 / 512) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(275 / 512)
  have hx61 : Bounds (237 / 512) (237 / 512) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-154052897 / 200000000) (-770264483 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-356548208877 / 1000000000000) (-356548207951 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (152130340191 / 500000000000) (152130341423 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (152130340191 / 1000000000000) (152130341423 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (152130340191 / 1000000000000) (152130341423 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-152130341423 / 1000000000000) (-152130340191 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (541016838577 / 1000000000000) (541016840809 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (541016838577 / 1000000000000) (541016840809 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (275 / 512)
  have hx71 : Bounds (541016838577 / 1000000000000) (541016840809 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(343 / 640)
  have hx73 : Bounds (983 / 640) (983 / 640) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 640) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(343 / 640)
  have hx74 : Bounds (983 / 640) (983 / 640) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 640) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (429140943 / 1000000000) (26821309 / 62500000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (659133667139 / 1000000000000) (26365346747 / 40000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(343 / 640)
  have hx77 : Bounds (-343 / 640) (-343 / 640) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 640) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (297 / 640) (297 / 640) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(343 / 640)
  have hx79 : Bounds (297 / 640) (297 / 640) x79 := by
    exact hx78
  let x80 : ℝ := -(343 / 640)
  have hx80 : Bounds (-343 / 640) (-343 / 640) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 640) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (297 / 640) (297 / 640) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(343 / 640)
  have hx82 : Bounds (297 / 640) (297 / 640) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-383868019 / 500000000) (-191934009 / 250000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-71255501027 / 200000000000) (-178138752103 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (75714040501 / 250000000000) (302856164469 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (75714040501 / 500000000000) (30285616447 / 200000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (75714040501 / 500000000000) (30285616447 / 200000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-30285616447 / 200000000000) (-75714040501 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (108343819553 / 200000000000) (270859549999 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (108343819553 / 200000000000) (270859549999 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (343 / 640)
  have hx92 : Bounds (108343819553 / 200000000000) (270859549999 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (541016838577 / 1000000000000) (270859549999 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (1234164018577 / 1000000000000) (617433140499 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (77135251161 / 125000000000) (617433140499 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (77135251161 / 125000000000) (617433140499 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(384143 / 1000000)
  have hx100 : Bounds (1384143 / 1000000) (1384143 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((384143 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(384143 / 1000000)
  have hx101 : Bounds (1384143 / 1000000) (1384143 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((384143 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (13003247 / 40000000) (40635147 / 125000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (56244854101 / 125000000000) (449958834193 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(384143 / 1000000)
  have hx104 : Bounds (-384143 / 1000000) (-384143 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((384143 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (615857 / 1000000) (615857 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(384143 / 1000000)
  have hx106 : Bounds (615857 / 1000000) (615857 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(384143 / 1000000)
  have hx107 : Bounds (-384143 / 1000000) (-384143 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((384143 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (615857 / 1000000) (615857 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(384143 / 1000000)
  have hx109 : Bounds (615857 / 1000000) (615857 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-242370243 / 500000000) (-96948097 / 200000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-298530821487 / 1000000000000) (-29853082087 / 100000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (151428011321 / 1000000000000) (151428013323 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (3785700283 / 50000000000) (37857003331 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (3785700283 / 50000000000) (37857003331 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-37857003331 / 500000000000) (-3785700283 / 50000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (308716586669 / 500000000000) (30871658767 / 50000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (308716586669 / 500000000000) (30871658767 / 50000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (384143 / 1000000)
  have hx119 : Bounds (308716586669 / 500000000000) (30871658767 / 50000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(38501 / 100000)
  have hx121 : Bounds (138501 / 100000) (138501 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((38501 / 100000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(38501 / 100000)
  have hx122 : Bounds (138501 / 100000) (138501 / 100000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((38501 / 100000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (325707359 / 1000000000) (2035671 / 6250000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (56388493661 / 125000000000) (225553975337 / 500000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(38501 / 100000)
  have hx125 : Bounds (-38501 / 100000) (-38501 / 100000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((38501 / 100000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (61499 / 100000) (61499 / 100000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(38501 / 100000)
  have hx127 : Bounds (61499 / 100000) (61499 / 100000) x127 := by
    exact hx126
  let x128 : ℝ := -(38501 / 100000)
  have hx128 : Bounds (-38501 / 100000) (-38501 / 100000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((38501 / 100000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (61499 / 100000) (61499 / 100000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(38501 / 100000)
  have hx130 : Bounds (61499 / 100000) (61499 / 100000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-60768659 / 125000000) (-486149271 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-74744235197 / 250000000000) (-74744235043 / 250000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (304262017 / 2000000000) (76065505251 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (304262017 / 4000000000) (76065505251 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (304262017 / 4000000000) (76065505251 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-76065505251 / 1000000000000) (-304262017 / 4000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (617081674749 / 1000000000000) (2468326707 / 4000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (617081674749 / 1000000000000) (2468326707 / 4000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (38501 / 100000)
  have hx140 : Bounds (617081674749 / 1000000000000) (2468326707 / 4000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (384143 / 1000000) (38501 / 100000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (38501 / 100000) ≤ (2468326707 / 4000000000) := hx140.2
      have h2 : (77135251161 / 125000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (617433140499 / 1000000000000) := hx98.2
      have h2 : (308716586669 / 500000000000) ≤ biasE (384143 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (930909090909 / 250000000000) (466472303207 / 125000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (229778900913 / 100000000000) (2304123673 / 1000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (229778900913 / 100000000000) (2304123673 / 1000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(141593 / 500000)
  have hx145 : Bounds (641593 / 500000) (641593 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((141593 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(141593 / 500000)
  have hx146 : Bounds (641593 / 500000) (641593 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((141593 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (249346047 / 1000000000) (487004 / 1953125) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (63991471333 / 200000000000) (319957357949 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(141593 / 500000)
  have hx149 : Bounds (-141593 / 500000) (-141593 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((141593 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (358407 / 500000) (358407 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(141593 / 500000)
  have hx151 : Bounds (358407 / 500000) (358407 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(141593 / 500000)
  have hx152 : Bounds (-141593 / 500000) (-141593 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((141593 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (358407 / 500000) (358407 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(141593 / 500000)
  have hx154 : Bounds (358407 / 500000) (358407 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-332938887 / 1000000000) (-166469443 / 500000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-238655255347 / 1000000000000) (-238655254629 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (40651050659 / 500000000000) (2032552583 / 25000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (40651050659 / 1000000000000) (2032552583 / 50000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (40651050659 / 1000000000000) (2032552583 / 50000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-2032552583 / 50000000000) (-40651050659 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (32624806417 / 50000000000) (652496130341 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (32624806417 / 50000000000) (652496130341 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (141593 / 500000)
  have hx164 : Bounds (32624806417 / 50000000000) (652496130341 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(7097 / 25000)
  have hx166 : Bounds (32097 / 25000) (32097 / 25000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7097 / 25000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(7097 / 25000)
  have hx167 : Bounds (32097 / 25000) (32097 / 25000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7097 / 25000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (124943371 / 500000000) (249886743 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (160412295159 / 500000000000) (320824591603 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(7097 / 25000)
  have hx170 : Bounds (-7097 / 25000) (-7097 / 25000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7097 / 25000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (17903 / 25000) (17903 / 25000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(7097 / 25000)
  have hx172 : Bounds (17903 / 25000) (17903 / 25000) x172 := by
    exact hx171
  let x173 : ℝ := -(7097 / 25000)
  have hx173 : Bounds (-7097 / 25000) (-7097 / 25000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7097 / 25000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (17903 / 25000) (17903 / 25000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(7097 / 25000)
  have hx175 : Bounds (17903 / 25000) (17903 / 25000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-333907529 / 1000000000) (-41738441 / 125000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-59779464917 / 250000000000) (-239117858951 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (1634134613 / 20000000000) (20426683163 / 250000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (1634134613 / 40000000000) (20426683163 / 500000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (1634134613 / 40000000000) (20426683163 / 500000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-20426683163 / 500000000000) (-1634134613 / 40000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (326146906837 / 500000000000) (26091752627 / 40000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (326146906837 / 500000000000) (26091752627 / 40000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (7097 / 25000)
  have hx185 : Bounds (326146906837 / 500000000000) (26091752627 / 40000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(141593 / 500000)
  have hx186 : Bounds (650701678339 / 1000000000000) (652495566463 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((141593 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(7097 / 25000)
  have hx187 : Bounds (652296343911 / 1000000000000) (163523657073 / 250000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((7097 / 25000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (141593 / 500000) (7097 / 25000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (141593 / 500000) ≤ (652495566463 / 1000000000000) := hx186.2
      have h2 : (32624806417 / 50000000000) ≤ biasE (141593 / 500000) := hx164.1
      linarith
    · have h1 : biasE (7097 / 25000) ≤ (26091752627 / 40000000000) := hx185.2
      have h2 : (652296343911 / 1000000000000) ≤ x143 * (7097 / 25000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1384143 / 1000000) (138501 / 100000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-38501 / 100000) (-384143 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (61499 / 100000) (615857 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (61499 / 100000) (615857 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (202969195771 / 125000000000) (813021349941 / 500000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (140469195771 / 62500000000) (563021349941 / 250000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (140469195771 / 62500000000) (563021349941 / 250000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (40491083 / 50000000) (101482079 / 125000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (40491083 / 100000000) (101482079 / 250000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (40491083 / 100000000) (101482079 / 250000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (641593 / 500000) (32097 / 25000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-7097 / 25000) (-141593 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (17903 / 25000) (358407 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (17903 / 25000) (358407 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (174382754801 / 125000000000) (698207004413 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (111882754801 / 62500000000) (448207004413 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (111882754801 / 62500000000) (448207004413 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (291142467 / 500000000) (18243571 / 31250000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (291142467 / 1000000000) (18243571 / 62500000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (291142467 / 1000000000) (18243571 / 62500000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (328319948957 / 250000000000) (328400513439 / 250000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (77135251161 / 62500000000) (617433140499 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-617433140499 / 500000000000) (-77135251161 / 62500000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (7841351483 / 100000000000) (3971901759 / 50000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (7841351483 / 100000000000) (3971901759 / 50000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (19442957621 / 125000000000) (9767903809 / 62500000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-9767903809 / 62500000000) (-19442957621 / 125000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-38936473057 / 500000000000) (-19026406447 / 250000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-38936473057 / 500000000000) (-19026406447 / 250000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (78017082953 / 1000000000000) (78390344141 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (144136839 / 1000000000000) (2284718353 / 1000000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (749 / 2048) (937 / 2560) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (749 / 2048) ≤ m → m ≤ (937 / 2560) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0261

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0262
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (937 / 2560) (3751 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (937 / 2560) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (937 / 1280) (3751 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3751 / 5120) (-937 / 1280) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1369 / 5120) (343 / 1280) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1369 / 5120) (343 / 1280) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (937 / 640) (3751 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3751 / 2560) (-937 / 640) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1369 / 2560) (343 / 640) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1369 / 2560) (343 / 640) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(343 / 1280)
  have hx9 : Bounds (1623 / 1280) (1623 / 1280) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 1280) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(343 / 1280)
  have hx10 : Bounds (1623 / 1280) (1623 / 1280) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 1280) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (23741621 / 100000000) (237416211 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (301036335023 / 1000000000000) (75259084073 / 250000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(343 / 1280)
  have hx13 : Bounds (-343 / 1280) (-343 / 1280) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 1280) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (937 / 1280) (937 / 1280) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(343 / 1280)
  have hx15 : Bounds (937 / 1280) (937 / 1280) x15 := by
    exact hx14
  let x16 : ℝ := -(343 / 1280)
  have hx16 : Bounds (-343 / 1280) (-343 / 1280) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 1280) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (937 / 1280) (937 / 1280) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(343 / 1280)
  have hx18 : Bounds (937 / 1280) (937 / 1280) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-12477283 / 40000000) (-155966037 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-114172013389 / 500000000000) (-45668805209 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (14538461649 / 200000000000) (72692310247 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (18173077061 / 500000000000) (9086538781 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (18173077061 / 500000000000) (9086538781 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-9086538781 / 250000000000) (-18173077061 / 500000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (164200256219 / 250000000000) (328400513439 / 500000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (164200256219 / 250000000000) (328400513439 / 500000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (343 / 1280)
  have hx28 : Bounds (164200256219 / 250000000000) (328400513439 / 500000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1369 / 5120)
  have hx30 : Bounds (6489 / 5120) (6489 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1369 / 5120)
  have hx31 : Bounds (6489 / 5120) (6489 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (59238499 / 250000000) (236953997 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (300311421883 / 1000000000000) (300311423151 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1369 / 5120)
  have hx34 : Bounds (-1369 / 5120) (-1369 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3751 / 5120) (3751 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1369 / 5120)
  have hx36 : Bounds (3751 / 5120) (3751 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(1369 / 5120)
  have hx37 : Bounds (-1369 / 5120) (-1369 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3751 / 5120) (3751 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1369 / 5120)
  have hx39 : Bounds (3751 / 5120) (3751 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-4861437 / 15625000) (-311131967 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-113970313669 / 500000000000) (-56985156651 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (14474158909 / 200000000000) (72370796547 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (4523174659 / 125000000000) (18092699137 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (4523174659 / 125000000000) (18092699137 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-18092699137 / 500000000000) (-4523174659 / 125000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (328480890863 / 500000000000) (41060111483 / 62500000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (328480890863 / 500000000000) (41060111483 / 62500000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1369 / 5120)
  have hx49 : Bounds (328480890863 / 500000000000) (41060111483 / 62500000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (164200256219 / 250000000000) (41060111483 / 62500000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(343 / 640)
  have hx52 : Bounds (983 / 640) (983 / 640) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 640) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(343 / 640)
  have hx53 : Bounds (983 / 640) (983 / 640) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((343 / 640) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (429140943 / 1000000000) (26821309 / 62500000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (659133667139 / 1000000000000) (26365346747 / 40000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(343 / 640)
  have hx56 : Bounds (-343 / 640) (-343 / 640) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 640) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (297 / 640) (297 / 640) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(343 / 640)
  have hx58 : Bounds (297 / 640) (297 / 640) x58 := by
    exact hx57
  let x59 : ℝ := -(343 / 640)
  have hx59 : Bounds (-343 / 640) (-343 / 640) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((343 / 640) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (297 / 640) (297 / 640) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(343 / 640)
  have hx61 : Bounds (297 / 640) (297 / 640) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-383868019 / 500000000) (-191934009 / 250000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-71255501027 / 200000000000) (-178138752103 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (75714040501 / 250000000000) (302856164469 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (75714040501 / 500000000000) (30285616447 / 200000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (75714040501 / 500000000000) (30285616447 / 200000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-30285616447 / 200000000000) (-75714040501 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (108343819553 / 200000000000) (270859549999 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (108343819553 / 200000000000) (270859549999 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (343 / 640)
  have hx71 : Bounds (108343819553 / 200000000000) (270859549999 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1369 / 2560)
  have hx73 : Bounds (3929 / 2560) (3929 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1369 / 2560)
  have hx74 : Bounds (3929 / 2560) (3929 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (214188841 / 500000000) (428377683 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (13149186817 / 20000000000) (328729671193 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1369 / 2560)
  have hx77 : Bounds (-1369 / 2560) (-1369 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1191 / 2560) (1191 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1369 / 2560)
  have hx79 : Bounds (1191 / 2560) (1191 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(1369 / 2560)
  have hx80 : Bounds (-1369 / 2560) (-1369 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1191 / 2560) (1191 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1369 / 2560)
  have hx82 : Bounds (1191 / 2560) (1191 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-765213969 / 1000000000) (-765213967 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-356003842609 / 1000000000000) (-178001920839 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (301455498241 / 1000000000000) (75363875177 / 250000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (58878027 / 390625000) (75363875177 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (58878027 / 390625000) (75363875177 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-75363875177 / 500000000000) (-58878027 / 390625000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (271209714823 / 500000000000) (13560485797 / 25000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (271209714823 / 500000000000) (13560485797 / 25000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1369 / 2560)
  have hx92 : Bounds (271209714823 / 500000000000) (13560485797 / 25000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (108343819553 / 200000000000) (13560485797 / 25000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (246973255553 / 200000000000) (15444582661 / 12500000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (308716569441 / 500000000000) (15444582661 / 25000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (308716569441 / 500000000000) (15444582661 / 25000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(383277 / 1000000)
  have hx100 : Bounds (1383277 / 1000000) (1383277 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((383277 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(383277 / 1000000)
  have hx101 : Bounds (1383277 / 1000000) (1383277 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((383277 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (324455321 / 1000000000) (162227661 / 500000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (224405791533 / 500000000000) (448811584451 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(383277 / 1000000)
  have hx104 : Bounds (-383277 / 1000000) (-383277 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((383277 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (616723 / 1000000) (616723 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(383277 / 1000000)
  have hx106 : Bounds (616723 / 1000000) (616723 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(383277 / 1000000)
  have hx107 : Bounds (-383277 / 1000000) (-383277 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((383277 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (616723 / 1000000) (616723 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(383277 / 1000000)
  have hx109 : Bounds (616723 / 1000000) (616723 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-483335303 / 1000000000) (-241667651 / 500000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-298083998073 / 1000000000000) (-59616799491 / 200000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (150727584993 / 1000000000000) (37681896749 / 250000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (4710237031 / 62500000000) (37681896749 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (4710237031 / 62500000000) (37681896749 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-37681896749 / 500000000000) (-4710237031 / 62500000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (308891693251 / 500000000000) (77222923563 / 125000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (308891693251 / 500000000000) (77222923563 / 125000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (383277 / 1000000)
  have hx119 : Bounds (308891693251 / 500000000000) (77222923563 / 125000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(24009 / 62500)
  have hx121 : Bounds (86509 / 62500) (86509 / 62500) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24009 / 62500) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(24009 / 62500)
  have hx122 : Bounds (86509 / 62500) (86509 / 62500) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24009 / 62500) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (162540949 / 500000000) (325081899 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (3599681269 / 8000000000) (44996016001 / 100000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(24009 / 62500)
  have hx125 : Bounds (-24009 / 62500) (-24009 / 62500) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24009 / 62500) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (38491 / 62500) (38491 / 62500) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(24009 / 62500)
  have hx127 : Bounds (38491 / 62500) (38491 / 62500) x127 := by
    exact hx126
  let x128 : ℝ := -(24009 / 62500)
  have hx128 : Bounds (-24009 / 62500) (-24009 / 62500) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24009 / 62500) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (38491 / 62500) (38491 / 62500) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(24009 / 62500)
  have hx130 : Bounds (38491 / 62500) (38491 / 62500) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-48474211 / 100000000) (-484742109 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-298531336897 / 1000000000000) (-7463283407 / 25000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (4732150679 / 31250000000) (15142882373 / 100000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (4732150679 / 62500000000) (15142882373 / 200000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (4732150679 / 62500000000) (15142882373 / 200000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-15142882373 / 200000000000) (-4732150679 / 62500000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (123486553627 / 200000000000) (77179096267 / 125000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (123486553627 / 200000000000) (77179096267 / 125000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (24009 / 62500)
  have hx140 : Bounds (123486553627 / 200000000000) (77179096267 / 125000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (383277 / 1000000) (24009 / 62500) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (24009 / 62500) ≤ (77179096267 / 125000000000) := hx140.2
      have h2 : (308716569441 / 500000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (15444582661 / 25000000000) := hx98.2
      have h2 : (308891693251 / 500000000000) ≤ biasE (383277 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (746355685131 / 200000000000) (3739956172389 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (576030916741 / 250000000000) (57762062253 / 25000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (576030916741 / 250000000000) (57762062253 / 25000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(282493 / 1000000)
  have hx145 : Bounds (1282493 / 1000000) (1282493 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((282493 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(282493 / 1000000)
  have hx146 : Bounds (1282493 / 1000000) (1282493 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((282493 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (248805839 / 1000000000) (3110073 / 12500000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (79772936719 / 250000000000) (997161713 / 3125000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(282493 / 1000000)
  have hx149 : Bounds (-282493 / 1000000) (-282493 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((282493 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (717507 / 1000000) (717507 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(282493 / 1000000)
  have hx151 : Bounds (717507 / 1000000) (717507 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(282493 / 1000000)
  have hx152 : Bounds (-282493 / 1000000) (-282493 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((282493 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (717507 / 1000000) (717507 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(282493 / 1000000)
  have hx154 : Bounds (717507 / 1000000) (717507 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-10374143 / 31250000) (-13278903 / 40000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-238192647089 / 1000000000000) (-23819264637 / 100000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (80899099787 / 1000000000000) (8089910179 / 100000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (40449549893 / 1000000000000) (8089910179 / 200000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (40449549893 / 1000000000000) (8089910179 / 200000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-8089910179 / 200000000000) (-40449549893 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (130539525821 / 200000000000) (652697631107 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (130539525821 / 200000000000) (652697631107 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (282493 / 1000000)
  have hx164 : Bounds (130539525821 / 200000000000) (652697631107 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(283187 / 1000000)
  have hx166 : Bounds (1283187 / 1000000) (1283187 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((283187 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(283187 / 1000000)
  have hx167 : Bounds (1283187 / 1000000) (1283187 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((283187 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (249346827 / 1000000000) (62336707 / 250000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (319958606897 / 1000000000000) (319958608181 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(283187 / 1000000)
  have hx170 : Bounds (-283187 / 1000000) (-283187 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((283187 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (716813 / 1000000) (716813 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(283187 / 1000000)
  have hx172 : Bounds (716813 / 1000000) (716813 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(283187 / 1000000)
  have hx173 : Bounds (-283187 / 1000000) (-283187 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((283187 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (716813 / 1000000) (716813 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(283187 / 1000000)
  have hx175 : Bounds (716813 / 1000000) (716813 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-166470141 / 500000000) (-332940281 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-119327961181 / 500000000000) (-59663980411 / 250000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (16260536907 / 200000000000) (81302686537 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (40651342267 / 1000000000000) (40651343269 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (40651342267 / 1000000000000) (40651343269 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-40651343269 / 1000000000000) (-40651342267 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (652495836731 / 1000000000000) (652495838733 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (652495836731 / 1000000000000) (652495838733 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (283187 / 1000000)
  have hx185 : Bounds (652495836731 / 1000000000000) (652495838733 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(282493 / 1000000)
  have hx186 : Bounds (650898807051 / 1000000000000) (326347565041 / 500000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((282493 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(283187 / 1000000)
  have hx187 : Bounds (163124467219 / 250000000000) (65429860493 / 100000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((283187 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (282493 / 1000000) (283187 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (282493 / 1000000) ≤ (326347565041 / 500000000000) := hx186.2
      have h2 : (130539525821 / 200000000000) ≤ biasE (282493 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (283187 / 1000000) ≤ (652495838733 / 1000000000000) := hx185.2
      have h2 : (163124467219 / 250000000000) ≤ x143 * (283187 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1383277 / 1000000) (86509 / 62500) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-24009 / 62500) (-383277 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (38491 / 62500) (616723 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (38491 / 62500) (616723 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (810736748913 / 500000000000) (1623756202749 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (560736748913 / 250000000000) (1123756202749 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (560736748913 / 250000000000) (1123756202749 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (807790623 / 1000000000) (101228001 / 125000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (807790623 / 2000000000) (101228001 / 250000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (807790623 / 2000000000) (101228001 / 250000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1282493 / 1000000) (1283187 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-283187 / 1000000) (-282493 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (716813 / 1000000) (717507 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (716813 / 1000000) (717507 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (69685731289 / 50000000000) (139506398461 / 100000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (44685731289 / 25000000000) (89506398461 / 50000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (44685731289 / 25000000000) (89506398461 / 50000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (116155683 / 200000000) (582287109 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (116155683 / 400000000) (582287109 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (116155683 / 400000000) (582287109 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (164200256219 / 125000000000) (41060111483 / 31250000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (308716569441 / 250000000000) (15444582661 / 12500000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-15444582661 / 12500000000) (-308716569441 / 250000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (9754429609 / 125000000000) (19764322423 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (9754429609 / 125000000000) (19764322423 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (30960756661 / 200000000000) (31108903373 / 200000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-31108903373 / 200000000000) (-30960756661 / 200000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-77509079993 / 1000000000000) (-75746493613 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-77509079993 / 1000000000000) (-75746493613 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (3882254151 / 50000000000) (7801737437 / 100000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (136003027 / 1000000000000) (2270880757 / 1000000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (937 / 2560) (3751 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (937 / 2560) ≤ m → m ≤ (3751 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0262

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0263
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3751 / 10240) (1877 / 5120) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (3751 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (3751 / 5120) (1877 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1877 / 2560) (-3751 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (683 / 2560) (1369 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (683 / 2560) (1369 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3751 / 2560) (1877 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1877 / 1280) (-3751 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (683 / 1280) (1369 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (683 / 1280) (1369 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1369 / 5120)
  have hx9 : Bounds (6489 / 5120) (6489 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1369 / 5120)
  have hx10 : Bounds (6489 / 5120) (6489 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (59238499 / 250000000) (236953997 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (300311421883 / 1000000000000) (300311423151 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1369 / 5120)
  have hx13 : Bounds (-1369 / 5120) (-1369 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3751 / 5120) (3751 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1369 / 5120)
  have hx15 : Bounds (3751 / 5120) (3751 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(1369 / 5120)
  have hx16 : Bounds (-1369 / 5120) (-1369 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3751 / 5120) (3751 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1369 / 5120)
  have hx18 : Bounds (3751 / 5120) (3751 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-4861437 / 15625000) (-311131967 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-113970313669 / 500000000000) (-56985156651 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (14474158909 / 200000000000) (72370796547 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (4523174659 / 125000000000) (18092699137 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (4523174659 / 125000000000) (18092699137 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-18092699137 / 500000000000) (-4523174659 / 125000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (328480890863 / 500000000000) (41060111483 / 62500000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (328480890863 / 500000000000) (41060111483 / 62500000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1369 / 5120)
  have hx28 : Bounds (328480890863 / 500000000000) (41060111483 / 62500000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(683 / 2560)
  have hx30 : Bounds (3243 / 2560) (3243 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(683 / 2560)
  have hx31 : Bounds (3243 / 2560) (3243 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (14780723 / 62500000) (236491569 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (149793389653 / 500000000000) (149793390287 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(683 / 2560)
  have hx34 : Bounds (-683 / 2560) (-683 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1877 / 2560) (1877 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(683 / 2560)
  have hx36 : Bounds (1877 / 2560) (1877 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(683 / 2560)
  have hx37 : Bounds (-683 / 2560) (-683 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1877 / 2560) (1877 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(683 / 2560)
  have hx39 : Bounds (1877 / 2560) (1877 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-310332501 / 1000000000) (-124133 / 400000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-227536759523 / 1000000000000) (-227536758789 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (72050019783 / 1000000000000) (14410004357 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (36025009891 / 1000000000000) (36025010893 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (36025009891 / 1000000000000) (36025010893 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-36025010893 / 1000000000000) (-36025009891 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (657122169107 / 1000000000000) (657122171109 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (657122169107 / 1000000000000) (657122171109 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (683 / 2560)
  have hx49 : Bounds (657122169107 / 1000000000000) (657122171109 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (328480890863 / 500000000000) (657122171109 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1369 / 2560)
  have hx52 : Bounds (3929 / 2560) (3929 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1369 / 2560)
  have hx53 : Bounds (3929 / 2560) (3929 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1369 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (214188841 / 500000000) (428377683 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (13149186817 / 20000000000) (328729671193 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1369 / 2560)
  have hx56 : Bounds (-1369 / 2560) (-1369 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1191 / 2560) (1191 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1369 / 2560)
  have hx58 : Bounds (1191 / 2560) (1191 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(1369 / 2560)
  have hx59 : Bounds (-1369 / 2560) (-1369 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1369 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1191 / 2560) (1191 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1369 / 2560)
  have hx61 : Bounds (1191 / 2560) (1191 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-765213969 / 1000000000) (-765213967 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-356003842609 / 1000000000000) (-178001920839 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (301455498241 / 1000000000000) (75363875177 / 250000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (58878027 / 390625000) (75363875177 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (58878027 / 390625000) (75363875177 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-75363875177 / 500000000000) (-58878027 / 390625000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (271209714823 / 500000000000) (13560485797 / 25000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (271209714823 / 500000000000) (13560485797 / 25000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1369 / 2560)
  have hx71 : Bounds (271209714823 / 500000000000) (13560485797 / 25000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(683 / 1280)
  have hx73 : Bounds (1963 / 1280) (1963 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(683 / 1280)
  have hx74 : Bounds (1963 / 1280) (1963 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (427613837 / 1000000000) (213806919 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (163946476959 / 250000000000) (655785909371 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(683 / 1280)
  have hx77 : Bounds (-683 / 1280) (-683 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (597 / 1280) (597 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(683 / 1280)
  have hx79 : Bounds (597 / 1280) (597 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(683 / 1280)
  have hx80 : Bounds (-683 / 1280) (-683 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (597 / 1280) (597 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(683 / 1280)
  have hx82 : Bounds (597 / 1280) (597 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-190674561 / 250000000) (-381349121 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-177863613933 / 500000000000) (-88931806733 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (30005867997 / 100000000000) (300058682439 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (30005867997 / 200000000000) (7501467061 / 50000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (30005867997 / 200000000000) (7501467061 / 50000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-7501467061 / 50000000000) (-30005867997 / 200000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (27155891939 / 50000000000) (108623568203 / 200000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (27155891939 / 50000000000) (108623568203 / 200000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (683 / 1280)
  have hx92 : Bounds (27155891939 / 50000000000) (108623568203 / 200000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (271209714823 / 500000000000) (108623568203 / 200000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (617783304823 / 500000000000) (247253004403 / 200000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (617783304823 / 1000000000000) (19316640969 / 31250000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (617783304823 / 1000000000000) (19316640969 / 31250000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(382411 / 1000000)
  have hx100 : Bounds (1382411 / 1000000) (1382411 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((382411 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(382411 / 1000000)
  have hx101 : Bounds (1382411 / 1000000) (1382411 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((382411 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (80957269 / 250000000) (323829077 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (223832438391 / 500000000000) (89532975633 / 200000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(382411 / 1000000)
  have hx104 : Bounds (-382411 / 1000000) (-382411 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((382411 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (617589 / 1000000) (617589 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(382411 / 1000000)
  have hx106 : Bounds (617589 / 1000000) (617589 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(382411 / 1000000)
  have hx107 : Bounds (-382411 / 1000000) (-382411 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((382411 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (617589 / 1000000) (617589 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(382411 / 1000000)
  have hx109 : Bounds (617589 / 1000000) (617589 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-120483023 / 250000000) (-481932091 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-297635958767 / 1000000000000) (-74408989537 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (30005783603 / 200000000000) (150028920017 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (75014459007 / 1000000000000) (75014460009 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (75014459007 / 1000000000000) (75014460009 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-75014460009 / 1000000000000) (-75014459007 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (618132719991 / 1000000000000) (618132721993 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (618132719991 / 1000000000000) (618132721993 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (382411 / 1000000)
  have hx119 : Bounds (618132719991 / 1000000000000) (618132721993 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(191639 / 500000)
  have hx121 : Bounds (691639 / 500000) (691639 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((191639 / 500000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(191639 / 500000)
  have hx122 : Bounds (691639 / 500000) (691639 / 500000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((191639 / 500000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (81114011 / 250000000) (64891209 / 200000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (28050806727 / 62500000000) (56101613627 / 125000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(191639 / 500000)
  have hx125 : Bounds (-191639 / 500000) (-191639 / 500000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((191639 / 500000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (308361 / 500000) (308361 / 500000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(191639 / 500000)
  have hx127 : Bounds (308361 / 500000) (308361 / 500000) x127 := by
    exact hx126
  let x128 : ℝ := -(191639 / 500000)
  have hx128 : Bounds (-191639 / 500000) (-191639 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((191639 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (308361 / 500000) (308361 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(191639 / 500000)
  have hx130 : Bounds (308361 / 500000) (308361 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-120834231 / 250000000) (-483336923 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-74521128611 / 250000000000) (-149042256913 / 500000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (37682098297 / 250000000000) (15072839519 / 100000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (37682098297 / 500000000000) (15072839519 / 200000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (37682098297 / 500000000000) (15072839519 / 200000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-15072839519 / 200000000000) (-37682098297 / 500000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (123556596481 / 200000000000) (308891492203 / 500000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (123556596481 / 200000000000) (308891492203 / 500000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (191639 / 500000)
  have hx140 : Bounds (123556596481 / 200000000000) (308891492203 / 500000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (382411 / 1000000) (191639 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (191639 / 500000) ≤ (308891492203 / 500000000000) := hx140.2
      have h2 : (617783304823 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (19316640969 / 31250000000) := hx98.2
      have h2 : (618132719991 / 1000000000000) ≤ biasE (382411 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (934989043097 / 250000000000) (1874084919473 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (2310482484071 / 1000000000000) (2316865634233 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (2310482484071 / 1000000000000) (2316865634233 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(140901 / 500000)
  have hx145 : Bounds (640901 / 500000) (640901 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((140901 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(140901 / 500000)
  have hx146 : Bounds (640901 / 500000) (640901 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((140901 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (2482669 / 10000000) (248266901 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (318229008953 / 1000000000000) (79557252559 / 250000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(140901 / 500000)
  have hx149 : Bounds (-140901 / 500000) (-140901 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((140901 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (359099 / 500000) (359099 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(140901 / 500000)
  have hx151 : Bounds (359099 / 500000) (359099 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(140901 / 500000)
  have hx152 : Bounds (-140901 / 500000) (-140901 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((140901 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (359099 / 500000) (359099 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(140901 / 500000)
  have hx154 : Bounds (359099 / 500000) (359099 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-165504991 / 500000000) (-331009981 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-237730707053 / 1000000000000) (-118865353167 / 500000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (804983019 / 10000000000) (40249151951 / 500000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (804983019 / 20000000000) (40249151951 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (804983019 / 20000000000) (40249151951 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-40249151951 / 1000000000000) (-804983019 / 20000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (652898028049 / 1000000000000) (13057960601 / 20000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (652898028049 / 1000000000000) (13057960601 / 20000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (140901 / 500000)
  have hx164 : Bounds (652898028049 / 1000000000000) (13057960601 / 20000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(141247 / 500000)
  have hx166 : Bounds (641247 / 500000) (641247 / 500000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((141247 / 500000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(141247 / 500000)
  have hx167 : Bounds (641247 / 500000) (641247 / 500000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((141247 / 500000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (248806619 / 1000000000) (12440331 / 50000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (319092996027 / 1000000000000) (319092997311 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(141247 / 500000)
  have hx170 : Bounds (-141247 / 500000) (-141247 / 500000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((141247 / 500000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (358753 / 500000) (358753 / 500000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(141247 / 500000)
  have hx172 : Bounds (358753 / 500000) (358753 / 500000) x172 := by
    exact hx171
  let x173 : ℝ := -(141247 / 500000)
  have hx173 : Bounds (-141247 / 500000) (-141247 / 500000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((141247 / 500000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (358753 / 500000) (358753 / 500000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(141247 / 500000)
  have hx175 : Bounds (358753 / 500000) (358753 / 500000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-33197397 / 100000000) (-331973969 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-238193315319 / 1000000000000) (-238193314601 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (20224920177 / 250000000000) (8089968271 / 100000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (20224920177 / 500000000000) (8089968271 / 200000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (20224920177 / 500000000000) (8089968271 / 200000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-8089968271 / 200000000000) (-20224920177 / 500000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (130539467729 / 200000000000) (326348670323 / 500000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (130539467729 / 200000000000) (326348670323 / 500000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (141247 / 500000)
  have hx185 : Bounds (130539467729 / 200000000000) (326348670323 / 500000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(140901 / 500000)
  have hx186 : Bounds (40693661561 / 62500000000) (652897369459 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((140901 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(141247 / 500000)
  have hx187 : Bounds (130539487771 / 200000000000) (327250320239 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((141247 / 500000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (140901 / 500000) (141247 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (140901 / 500000) ≤ (652897369459 / 1000000000000) := hx186.2
      have h2 : (652898028049 / 1000000000000) ≤ biasE (140901 / 500000) := hx164.1
      linarith
    · have h1 : biasE (141247 / 500000) ≤ (326348670323 / 500000000000) := hx185.2
      have h2 : (130539487771 / 200000000000) ≤ x143 * (141247 / 500000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1382411 / 1000000) (691639 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-191639 / 500000) (-382411 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (308361 / 500000) (617589 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (308361 / 500000) (617589 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1619199823831 / 1000000000000) (1621476127007 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (1119199823831 / 500000000000) (1121476127007 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (1119199823831 / 500000000000) (1121476127007 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (402880583 / 500000000) (80779297 / 100000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (402880583 / 1000000000) (80779297 / 200000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (402880583 / 1000000000) (80779297 / 200000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (640901 / 500000) (641247 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-141247 / 500000) (-140901 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (358753 / 500000) (359099 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (358753 / 500000) (359099 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (69618684541 / 50000000000) (43553642757 / 31250000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (44618684541 / 25000000000) (27928642757 / 15625000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (44618684541 / 25000000000) (27928642757 / 15625000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (289638441 / 500000000) (580780589 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (289638441 / 1000000000) (580780589 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (289638441 / 1000000000) (580780589 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (328480890863 / 250000000000) (657122171109 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (617783304823 / 500000000000) (19316640969 / 15625000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-19316640969 / 15625000000) (-617783304823 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (19414635359 / 250000000000) (19669433143 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (19414635359 / 250000000000) (19669433143 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (1232527733 / 8000000000) (77402318489 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-77402318489 / 500000000000) (-1232527733 / 8000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-38573047771 / 500000000000) (-75388234053 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-38573047771 / 500000000000) (-75388234053 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (38637315469 / 500000000000) (77645373667 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (32133849 / 250000000000) (1128569807 / 500000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3751 / 10240) (1877 / 5120) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3751 / 10240) ≤ m → m ≤ (1877 / 5120) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0263

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0264
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1877 / 5120) (3757 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (1877 / 5120) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1877 / 2560) (3757 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3757 / 5120) (-1877 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1363 / 5120) (683 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1363 / 5120) (683 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1877 / 1280) (3757 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3757 / 2560) (-1877 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1363 / 2560) (683 / 1280) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1363 / 2560) (683 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(683 / 2560)
  have hx9 : Bounds (3243 / 2560) (3243 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(683 / 2560)
  have hx10 : Bounds (3243 / 2560) (3243 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (14780723 / 62500000) (236491569 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (149793389653 / 500000000000) (149793390287 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(683 / 2560)
  have hx13 : Bounds (-683 / 2560) (-683 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1877 / 2560) (1877 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(683 / 2560)
  have hx15 : Bounds (1877 / 2560) (1877 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(683 / 2560)
  have hx16 : Bounds (-683 / 2560) (-683 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1877 / 2560) (1877 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(683 / 2560)
  have hx18 : Bounds (1877 / 2560) (1877 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-310332501 / 1000000000) (-124133 / 400000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-227536759523 / 1000000000000) (-227536758789 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (72050019783 / 1000000000000) (14410004357 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (36025009891 / 1000000000000) (36025010893 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (36025009891 / 1000000000000) (36025010893 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-36025010893 / 1000000000000) (-36025009891 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (657122169107 / 1000000000000) (657122171109 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (657122169107 / 1000000000000) (657122171109 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (683 / 2560)
  have hx28 : Bounds (657122169107 / 1000000000000) (657122171109 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1363 / 5120)
  have hx30 : Bounds (6483 / 5120) (6483 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1363 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1363 / 5120)
  have hx31 : Bounds (6483 / 5120) (6483 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1363 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (236028927 / 1000000000) (460994 / 1953125) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (298862408933 / 1000000000000) (1494312051 / 5000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1363 / 5120)
  have hx34 : Bounds (-1363 / 5120) (-1363 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1363 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3757 / 5120) (3757 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1363 / 5120)
  have hx36 : Bounds (3757 / 5120) (3757 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(1363 / 5120)
  have hx37 : Bounds (-1363 / 5120) (-1363 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1363 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3757 / 5120) (3757 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1363 / 5120)
  have hx39 : Bounds (3757 / 5120) (3757 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-309533673 / 1000000000) (-38691709 / 125000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-227132423723 / 1000000000000) (-227132422989 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (7172998521 / 100000000000) (71729987211 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (7172998521 / 200000000000) (17932496803 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (7172998521 / 200000000000) (17932496803 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-17932496803 / 500000000000) (-7172998521 / 200000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (328641093197 / 500000000000) (131456437679 / 200000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (328641093197 / 500000000000) (131456437679 / 200000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1363 / 5120)
  have hx49 : Bounds (328641093197 / 500000000000) (131456437679 / 200000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (657122169107 / 1000000000000) (131456437679 / 200000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(683 / 1280)
  have hx52 : Bounds (1963 / 1280) (1963 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(683 / 1280)
  have hx53 : Bounds (1963 / 1280) (1963 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((683 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (427613837 / 1000000000) (213806919 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (163946476959 / 250000000000) (655785909371 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(683 / 1280)
  have hx56 : Bounds (-683 / 1280) (-683 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (597 / 1280) (597 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(683 / 1280)
  have hx58 : Bounds (597 / 1280) (597 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(683 / 1280)
  have hx59 : Bounds (-683 / 1280) (-683 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((683 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (597 / 1280) (597 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(683 / 1280)
  have hx61 : Bounds (597 / 1280) (597 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-190674561 / 250000000) (-381349121 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-177863613933 / 500000000000) (-88931806733 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (30005867997 / 100000000000) (300058682439 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (30005867997 / 200000000000) (7501467061 / 50000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (30005867997 / 200000000000) (7501467061 / 50000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-7501467061 / 50000000000) (-30005867997 / 200000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (27155891939 / 50000000000) (108623568203 / 200000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (27155891939 / 50000000000) (108623568203 / 200000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (683 / 1280)
  have hx71 : Bounds (27155891939 / 50000000000) (108623568203 / 200000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1363 / 2560)
  have hx73 : Bounds (3923 / 2560) (3923 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1363 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1363 / 2560)
  have hx74 : Bounds (3923 / 2560) (3923 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1363 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (3334761 / 7812500) (426849409 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (13082267403 / 20000000000) (654113371683 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1363 / 2560)
  have hx77 : Bounds (-1363 / 2560) (-1363 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1363 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1197 / 2560) (1197 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1363 / 2560)
  have hx79 : Bounds (1197 / 2560) (1197 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(1363 / 2560)
  have hx80 : Bounds (-1363 / 2560) (-1363 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1363 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1197 / 2560) (1197 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1363 / 2560)
  have hx82 : Bounds (1197 / 2560) (1197 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-760188833 / 1000000000) (-760188831 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-355447669181 / 1000000000000) (-88861917061 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (298665700969 / 1000000000000) (298665703439 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (37333212621 / 250000000000) (3733321293 / 25000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (37333212621 / 250000000000) (3733321293 / 25000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-3733321293 / 25000000000) (-37333212621 / 250000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (13595358207 / 25000000000) (135953582629 / 250000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (13595358207 / 25000000000) (135953582629 / 250000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1363 / 2560)
  have hx92 : Bounds (13595358207 / 25000000000) (135953582629 / 250000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (27155891939 / 50000000000) (135953582629 / 250000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (61813250939 / 50000000000) (309240377879 / 250000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (61813250939 / 100000000000) (309240377879 / 500000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (61813250939 / 100000000000) (309240377879 / 500000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(190773 / 500000)
  have hx100 : Bounds (690773 / 500000) (690773 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((190773 / 500000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(190773 / 500000)
  have hx101 : Bounds (690773 / 500000) (690773 / 500000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((190773 / 500000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (323203161 / 1000000000) (161601581 / 500000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (223260017133 / 500000000000) (446520035649 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(190773 / 500000)
  have hx104 : Bounds (-190773 / 500000) (-190773 / 500000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((190773 / 500000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (309227 / 500000) (309227 / 500000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(190773 / 500000)
  have hx106 : Bounds (309227 / 500000) (309227 / 500000) x106 := by
    exact hx105
  let x107 : ℝ := -(190773 / 500000)
  have hx107 : Bounds (-190773 / 500000) (-190773 / 500000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((190773 / 500000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (309227 / 500000) (309227 / 500000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(190773 / 500000)
  have hx109 : Bounds (309227 / 500000) (309227 / 500000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-30033279 / 62500000) (-480532463 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-297187224491 / 1000000000000) (-4643550373 / 15625000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (5973312391 / 40000000000) (149332811777 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (74666404887 / 1000000000000) (74666405889 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (74666404887 / 1000000000000) (74666405889 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-74666405889 / 1000000000000) (-74666404887 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (618480774111 / 1000000000000) (618480776113 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (618480774111 / 1000000000000) (618480776113 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (190773 / 500000)
  have hx119 : Bounds (618480774111 / 1000000000000) (618480776113 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(95603 / 250000)
  have hx121 : Bounds (345603 / 250000) (345603 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((95603 / 250000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(95603 / 250000)
  have hx122 : Bounds (345603 / 250000) (345603 / 250000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((95603 / 250000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (323829799 / 1000000000) (1619149 / 5000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (89533240019 / 200000000000) (223833100739 / 500000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(95603 / 250000)
  have hx125 : Bounds (-95603 / 250000) (-95603 / 250000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((95603 / 250000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (154397 / 250000) (154397 / 250000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(95603 / 250000)
  have hx127 : Bounds (154397 / 250000) (154397 / 250000) x127 := by
    exact hx126
  let x128 : ℝ := -(95603 / 250000)
  have hx128 : Bounds (-95603 / 250000) (-95603 / 250000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((95603 / 250000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (154397 / 250000) (154397 / 250000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(95603 / 250000)
  have hx130 : Bounds (154397 / 250000) (154397 / 250000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-481933711 / 1000000000) (-48193371 / 100000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-29763647671 / 100000000000) (-297636476091 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (30005944677 / 200000000000) (150029725387 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (18753715423 / 250000000000) (37507431347 / 500000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (18753715423 / 250000000000) (37507431347 / 500000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-37507431347 / 500000000000) (-18753715423 / 250000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (309066158653 / 500000000000) (154533079827 / 250000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (309066158653 / 500000000000) (154533079827 / 250000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (95603 / 250000)
  have hx140 : Bounds (309066158653 / 500000000000) (154533079827 / 250000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (190773 / 500000) (95603 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (95603 / 250000) ≤ (154533079827 / 250000000000) := hx140.2
      have h2 : (61813250939 / 100000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (309240377879 / 500000000000) := hx98.2
      have h2 : (618480774111 / 1000000000000) ≤ biasE (190773 / 500000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (749633967789 / 200000000000) (375641966251 / 100000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1158432814083 / 500000000000) (1161636635907 / 500000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1158432814083 / 500000000000) (1161636635907 / 500000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(281111 / 1000000)
  have hx145 : Bounds (1281111 / 1000000) (1281111 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((281111 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(281111 / 1000000)
  have hx146 : Bounds (1281111 / 1000000) (1281111 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((281111 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (24772767 / 100000000) (247727671 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (317366643041 / 1000000000000) (317366644323 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(281111 / 1000000)
  have hx149 : Bounds (-281111 / 1000000) (-281111 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((281111 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (718889 / 1000000) (718889 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(281111 / 1000000)
  have hx151 : Bounds (718889 / 1000000) (718889 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(281111 / 1000000)
  have hx152 : Bounds (-281111 / 1000000) (-281111 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((281111 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (718889 / 1000000) (718889 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(281111 / 1000000)
  have hx154 : Bounds (718889 / 1000000) (718889 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-66009663 / 200000000) (-165024157 / 500000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-237268103123 / 1000000000000) (-237268102403 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (40049269959 / 500000000000) (500615887 / 6250000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (40049269959 / 1000000000000) (500615887 / 12500000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (40049269959 / 1000000000000) (500615887 / 12500000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-500615887 / 12500000000) (-40049269959 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (8163723863 / 12500000000) (653097911041 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (8163723863 / 12500000000) (653097911041 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (281111 / 1000000)
  have hx164 : Bounds (8163723863 / 12500000000) (653097911041 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(281803 / 1000000)
  have hx166 : Bounds (1281803 / 1000000) (1281803 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((281803 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(281803 / 1000000)
  have hx167 : Bounds (1281803 / 1000000) (1281803 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((281803 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (1551673 / 6250000) (248267681 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (318230257027 / 1000000000000) (318230258309 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(281803 / 1000000)
  have hx170 : Bounds (-281803 / 1000000) (-281803 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((281803 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (718197 / 1000000) (718197 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(281803 / 1000000)
  have hx172 : Bounds (718197 / 1000000) (718197 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(281803 / 1000000)
  have hx173 : Bounds (-281803 / 1000000) (-281803 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((281803 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (718197 / 1000000) (718197 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(281803 / 1000000)
  have hx175 : Bounds (718197 / 1000000) (718197 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-2648091 / 8000000) (-165505687 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-237731376491 / 1000000000000) (-59432843943 / 250000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (10062360067 / 125000000000) (80498882537 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (10062360067 / 250000000000) (40249441269 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (10062360067 / 250000000000) (40249441269 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-40249441269 / 1000000000000) (-10062360067 / 250000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (652897738731 / 1000000000000) (163224435183 / 250000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (652897738731 / 1000000000000) (163224435183 / 250000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (281803 / 1000000)
  have hx185 : Bounds (652897738731 / 1000000000000) (163224435183 / 250000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(281111 / 1000000)
  have hx186 : Bounds (651296413599 / 1000000000000) (653097672713 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((281111 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(281803 / 1000000)
  have hx187 : Bounds (326449842307 / 500000000000) (327352688909 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((281803 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (281111 / 1000000) (281803 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (281111 / 1000000) ≤ (653097672713 / 1000000000000) := hx186.2
      have h2 : (8163723863 / 12500000000) ≤ biasE (281111 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (281803 / 1000000) ≤ (163224435183 / 250000000000) := hx185.2
      have h2 : (326449842307 / 500000000000) ≤ x143 * (281803 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (690773 / 500000) (345603 / 250000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-95603 / 250000) (-190773 / 500000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (154397 / 250000) (309227 / 500000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (154397 / 250000) (309227 / 500000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (404233782949 / 250000000000) (404800611411 / 250000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (279233782949 / 125000000000) (279800611411 / 125000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (279233782949 / 125000000000) (279800611411 / 125000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (100466953 / 125000000) (805763511 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (100466953 / 250000000) (805763511 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (100466953 / 250000000) (805763511 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1281111 / 1000000) (1281803 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-281803 / 1000000) (-281111 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (718197 / 1000000) (718889 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (718197 / 1000000) (718889 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (173879416711 / 125000000000) (174046953691 / 125000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (111379416711 / 62500000000) (111546953691 / 62500000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (111379416711 / 62500000000) (111546953691 / 62500000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (36110999 / 62500000) (115855811 / 200000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (36110999 / 125000000) (115855811 / 400000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (36110999 / 125000000) (115855811 / 400000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (657122169107 / 500000000000) (131456437679 / 100000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (61813250939 / 50000000000) (309240377879 / 250000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-309240377879 / 250000000000) (-61813250939 / 50000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (38641413349 / 500000000000) (7829935801 / 100000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (38641413349 / 500000000000) (7829935801 / 100000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (153331056197 / 1000000000000) (30813363577 / 200000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-30813363577 / 200000000000) (-153331056197 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-76783991187 / 1000000000000) (-75031698187 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-76783991187 / 1000000000000) (-75031698187 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (38452571591 / 500000000000) (38637460407 / 500000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (24230399 / 200000000000) (2243222627 / 1000000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1877 / 5120) (3757 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1877 / 5120) ≤ m → m ≤ (3757 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0264

end


