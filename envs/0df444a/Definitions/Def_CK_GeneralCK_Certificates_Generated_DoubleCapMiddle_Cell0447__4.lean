-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0447__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0447__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:43:38.051968+00:00
-- url     : https://prove2.me/theorems/d8aded21-c238-4184-b8d1-e3e09c08845b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0447 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0448, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0449, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0450).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0441Logs__8
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0449Logs__7

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0447
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (8111 / 20480) (4057 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (8111 / 20480) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (8111 / 10240) (4057 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-4057 / 5120) (-8111 / 10240) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1063 / 5120) (2129 / 10240) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1063 / 5120) (2129 / 10240) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (8111 / 5120) (4057 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-4057 / 2560) (-8111 / 5120) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1063 / 2560) (2129 / 5120) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1063 / 2560) (2129 / 5120) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2129 / 10240)
  have hx9 : Bounds (12369 / 10240) (12369 / 10240) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2129 / 10240) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2129 / 10240)
  have hx10 : Bounds (12369 / 10240) (12369 / 10240) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2129 / 10240) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (94445861 / 500000000) (188891723 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (45632845887 / 200000000000) (57041057661 / 250000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2129 / 10240)
  have hx13 : Bounds (-2129 / 10240) (-2129 / 10240) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2129 / 10240) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (8111 / 10240) (8111 / 10240) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2129 / 10240)
  have hx15 : Bounds (8111 / 10240) (8111 / 10240) x15 := by
    exact hx14
  let x16 : ℝ := -(2129 / 10240)
  have hx16 : Bounds (-2129 / 10240) (-2129 / 10240) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2129 / 10240) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (8111 / 10240) (8111 / 10240) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2129 / 10240)
  have hx18 : Bounds (8111 / 10240) (8111 / 10240) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-46616091 / 200000000) (-116540227 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-184620661183 / 1000000000000) (-18462066039 / 100000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (10885892063 / 250000000000) (21771785127 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (10885892063 / 500000000000) (21771785127 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (10885892063 / 500000000000) (21771785127 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-21771785127 / 1000000000000) (-10885892063 / 500000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (671375394873 / 1000000000000) (335687698437 / 500000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (671375394873 / 1000000000000) (335687698437 / 500000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2129 / 10240)
  have hx28 : Bounds (671375394873 / 1000000000000) (335687698437 / 500000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1063 / 5120)
  have hx30 : Bounds (6183 / 5120) (6183 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1063 / 5120)
  have hx31 : Bounds (6183 / 5120) (6183 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (188649151 / 1000000000) (2947643 / 15625000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (113907978577 / 500000000000) (227815958363 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1063 / 5120)
  have hx34 : Bounds (-1063 / 5120) (-1063 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (4057 / 5120) (4057 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1063 / 5120)
  have hx36 : Bounds (4057 / 5120) (4057 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(1063 / 5120)
  have hx37 : Bounds (-1063 / 5120) (-1063 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (4057 / 5120) (4057 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1063 / 5120)
  have hx39 : Bounds (4057 / 5120) (4057 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-46542131 / 200000000) (-116355327 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-46098980827 / 250000000000) (-36879184503 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (21710016923 / 500000000000) (5427504481 / 125000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (21710016923 / 1000000000000) (5427504481 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (21710016923 / 1000000000000) (5427504481 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-5427504481 / 250000000000) (-21710016923 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (167859290519 / 250000000000) (671437164077 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (167859290519 / 250000000000) (671437164077 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1063 / 5120)
  have hx49 : Bounds (167859290519 / 250000000000) (671437164077 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (671375394873 / 1000000000000) (671437164077 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2129 / 5120)
  have hx52 : Bounds (7249 / 5120) (7249 / 5120) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2129 / 5120) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2129 / 5120)
  have hx53 : Bounds (7249 / 5120) (7249 / 5120) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2129 / 5120) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (347709089 / 1000000000) (34770909 / 100000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (492293591047 / 1000000000000) (492293592463 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2129 / 5120)
  have hx56 : Bounds (-2129 / 5120) (-2129 / 5120) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2129 / 5120) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2991 / 5120) (2991 / 5120) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2129 / 5120)
  have hx58 : Bounds (2991 / 5120) (2991 / 5120) x58 := by
    exact hx57
  let x59 : ℝ := -(2129 / 5120)
  have hx59 : Bounds (-2129 / 5120) (-2129 / 5120) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2129 / 5120) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2991 / 5120) (2991 / 5120) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2129 / 5120)
  have hx61 : Bounds (2991 / 5120) (2991 / 5120) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-26877333 / 50000000) (-537546659 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-19626489991 / 62500000000) (-314023839271 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (178269751191 / 1000000000000) (22283719149 / 125000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (17826975119 / 200000000000) (22283719149 / 250000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (17826975119 / 200000000000) (22283719149 / 250000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-22283719149 / 250000000000) (-17826975119 / 200000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (151003075851 / 250000000000) (120802461081 / 200000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (151003075851 / 250000000000) (120802461081 / 200000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2129 / 5120)
  have hx71 : Bounds (151003075851 / 250000000000) (120802461081 / 200000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1063 / 2560)
  have hx73 : Bounds (3623 / 2560) (3623 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1063 / 2560)
  have hx74 : Bounds (3623 / 2560) (3623 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (347295153 / 1000000000) (173647577 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (122876009699 / 250000000000) (122876010053 / 250000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1063 / 2560)
  have hx77 : Bounds (-1063 / 2560) (-1063 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1497 / 2560) (1497 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1063 / 2560)
  have hx79 : Bounds (1497 / 2560) (1497 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(1063 / 2560)
  have hx80 : Bounds (-1063 / 2560) (-1063 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1497 / 2560) (1497 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1063 / 2560)
  have hx82 : Bounds (1497 / 2560) (1497 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-268272077 / 500000000) (-536544153 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-156876288777 / 500000000000) (-313752576969 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (88875730621 / 500000000000) (177751463243 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (88875730621 / 1000000000000) (44437865811 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (88875730621 / 1000000000000) (44437865811 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-44437865811 / 500000000000) (-88875730621 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (302135724189 / 500000000000) (604271450379 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (302135724189 / 500000000000) (604271450379 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1063 / 2560)
  have hx92 : Bounds (302135724189 / 500000000000) (604271450379 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (151003075851 / 250000000000) (604271450379 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (324289870851 / 250000000000) (1297418631379 / 1000000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (324289870851 / 500000000000) (64870931569 / 100000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (324289870851 / 500000000000) (64870931569 / 100000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(29589 / 100000)
  have hx100 : Bounds (129589 / 100000) (129589 / 100000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((29589 / 100000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(29589 / 100000)
  have hx101 : Bounds (129589 / 100000) (129589 / 100000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((29589 / 100000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (259197717 / 1000000000) (129598859 / 500000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (335891729483 / 1000000000000) (16794586539 / 50000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(29589 / 100000)
  have hx104 : Bounds (-29589 / 100000) (-29589 / 100000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((29589 / 100000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (70411 / 100000) (70411 / 100000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(29589 / 100000)
  have hx106 : Bounds (70411 / 100000) (70411 / 100000) x106 := by
    exact hx105
  let x107 : ℝ := -(29589 / 100000)
  have hx107 : Bounds (-29589 / 100000) (-29589 / 100000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((29589 / 100000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (70411 / 100000) (70411 / 100000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(29589 / 100000)
  have hx109 : Bounds (70411 / 100000) (70411 / 100000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-175410343 / 500000000) (-70164137 / 200000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-12350817661 / 50000000000) (-49403270503 / 200000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (88875376263 / 1000000000000) (17775075653 / 200000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (44437688131 / 1000000000000) (44437689133 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (44437688131 / 1000000000000) (44437689133 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-44437689133 / 1000000000000) (-44437688131 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (648709490867 / 1000000000000) (648709492869 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (648709490867 / 1000000000000) (648709492869 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (29589 / 100000)
  have hx119 : Bounds (648709490867 / 1000000000000) (648709492869 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(74079 / 250000)
  have hx121 : Bounds (324079 / 250000) (324079 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((74079 / 250000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(74079 / 250000)
  have hx122 : Bounds (324079 / 250000) (324079 / 250000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((74079 / 250000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (51905279 / 200000000) (64881599 / 250000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (16821410913 / 50000000000) (168214109779 / 500000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(74079 / 250000)
  have hx125 : Bounds (-74079 / 250000) (-74079 / 250000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((74079 / 250000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (175921 / 250000) (175921 / 250000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(74079 / 250000)
  have hx127 : Bounds (175921 / 250000) (175921 / 250000) x127 := by
    exact hx126
  let x128 : ℝ := -(74079 / 250000)
  have hx128 : Bounds (-74079 / 250000) (-74079 / 250000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((74079 / 250000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (175921 / 250000) (175921 / 250000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(74079 / 250000)
  have hx130 : Bounds (175921 / 250000) (175921 / 250000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-10982059 / 31250000) (-351425887 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-61823193643 / 250000000000) (-247292773867 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (11141930461 / 125000000000) (89135445691 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (11141930461 / 250000000000) (22283861423 / 500000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (11141930461 / 250000000000) (22283861423 / 500000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-22283861423 / 500000000000) (-11141930461 / 250000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (324289728577 / 500000000000) (162144864789 / 250000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (324289728577 / 500000000000) (162144864789 / 250000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (74079 / 250000)
  have hx140 : Bounds (324289728577 / 500000000000) (162144864789 / 250000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (29589 / 100000) (74079 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (74079 / 250000) ≤ (162144864789 / 250000000000) := hx140.2
      have h2 : (324289870851 / 500000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (64870931569 / 100000000000) := hx98.2
      have h2 : (648709490867 / 1000000000000) ≤ biasE (29589 / 100000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (4809769844997 / 1000000000000) (2408278457197 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1559759641857 / 500000000000) (3124545339919 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1559759641857 / 500000000000) (3124545339919 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(26803 / 125000)
  have hx145 : Bounds (151803 / 125000) (151803 / 125000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26803 / 125000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(26803 / 125000)
  have hx146 : Bounds (151803 / 125000) (151803 / 125000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26803 / 125000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (19426989 / 100000000) (194269891 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (235926016893 / 1000000000000) (58981504527 / 250000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(26803 / 125000)
  have hx149 : Bounds (-26803 / 125000) (-26803 / 125000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26803 / 125000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (98197 / 125000) (98197 / 125000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(26803 / 125000)
  have hx151 : Bounds (98197 / 125000) (98197 / 125000) x151 := by
    exact hx150
  let x152 : ℝ := -(26803 / 125000)
  have hx152 : Bounds (-26803 / 125000) (-26803 / 125000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26803 / 125000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (98197 / 125000) (98197 / 125000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(26803 / 125000)
  have hx154 : Bounds (98197 / 125000) (98197 / 125000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-241338073 / 1000000000) (-30167259 / 125000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-47397349509 / 250000000000) (-189589397249 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (46336618857 / 1000000000000) (46336620859 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (5792077357 / 250000000000) (2316831043 / 100000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (5792077357 / 250000000000) (2316831043 / 100000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-2316831043 / 100000000000) (-5792077357 / 250000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (66997886957 / 100000000000) (167494717893 / 250000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (66997886957 / 100000000000) (167494717893 / 250000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (26803 / 125000)
  have hx164 : Bounds (66997886957 / 100000000000) (167494717893 / 250000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(53687 / 250000)
  have hx166 : Bounds (303687 / 250000) (303687 / 250000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53687 / 250000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(53687 / 250000)
  have hx167 : Bounds (303687 / 250000) (303687 / 250000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53687 / 250000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (194536647 / 1000000000) (24317081 / 125000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (236313002869 / 1000000000000) (47262600817 / 200000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(53687 / 250000)
  have hx170 : Bounds (-53687 / 250000) (-53687 / 250000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53687 / 250000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (196313 / 250000) (196313 / 250000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(53687 / 250000)
  have hx172 : Bounds (196313 / 250000) (196313 / 250000) x172 := by
    exact hx171
  let x173 : ℝ := -(53687 / 250000)
  have hx173 : Bounds (-53687 / 250000) (-53687 / 250000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53687 / 250000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (196313 / 250000) (196313 / 250000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(53687 / 250000)
  have hx175 : Bounds (196313 / 250000) (196313 / 250000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-120875297 / 500000000) (-241750593 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-1186469609 / 6250000000) (-94917568327 / 500000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (46477865429 / 1000000000000) (46477867431 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (11619466357 / 500000000000) (5809733429 / 250000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (11619466357 / 500000000000) (5809733429 / 250000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-5809733429 / 250000000000) (-11619466357 / 500000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (167477061571 / 250000000000) (334954124143 / 500000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (167477061571 / 250000000000) (334954124143 / 500000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (53687 / 250000)
  have hx185 : Bounds (167477061571 / 250000000000) (334954124143 / 500000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(26803 / 125000)
  have hx186 : Bounds (668899802891 / 1000000000000) (669977509967 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((26803 / 125000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(53687 / 250000)
  have hx187 : Bounds (669910527139 / 1000000000000) (670989862657 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((53687 / 250000) : ℝ)) <;> norm_num
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
  have hc : Bounds (26803 / 125000) (53687 / 250000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (26803 / 125000) ≤ (669977509967 / 1000000000000) := hx186.2
      have h2 : (66997886957 / 100000000000) ≤ biasE (26803 / 125000) := hx164.1
      linarith
    · have h1 : biasE (53687 / 250000) ≤ (334954124143 / 500000000000) := hx185.2
      have h2 : (669910527139 / 1000000000000) ≤ x143 * (53687 / 250000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (129589 / 100000) (324079 / 250000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-74079 / 250000) (-29589 / 100000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (175921 / 250000) (70411 / 100000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (175921 / 250000) (70411 / 100000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (284046526821 / 200000000000) (1421092422167 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (184046526821 / 100000000000) (921092422167 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (184046526821 / 100000000000) (921092422167 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (305009201 / 500000000) (610952283 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (305009201 / 1000000000) (610952283 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (305009201 / 1000000000) (610952283 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (151803 / 125000) (303687 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-53687 / 250000) (-26803 / 125000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (196313 / 250000) (98197 / 125000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (196313 / 250000) (98197 / 125000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (636475656079 / 500000000000) (79592283751 / 62500000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (386475656079 / 250000000000) (48342283751 / 31250000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (386475656079 / 250000000000) (48342283751 / 31250000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (217803981 / 500000000) (218143621 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (217803981 / 1000000000) (218143621 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (217803981 / 1000000000) (218143621 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (671375394873 / 500000000000) (671437164077 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (324289870851 / 250000000000) (64870931569 / 50000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-64870931569 / 50000000000) (-324289870851 / 250000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (22666079183 / 500000000000) (182859379 / 4000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (22666079183 / 500000000000) (182859379 / 4000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (90249172483 / 1000000000000) (18103493669 / 200000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-18103493669 / 200000000000) (-90249172483 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-45185309979 / 1000000000000) (-44534327733 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-45185309979 / 1000000000000) (-44534327733 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (45219849961 / 1000000000000) (5669284291 / 125000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (17269991 / 500000000000) (163989319 / 200000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (8111 / 20480) (4057 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (8111 / 20480) ≤ m → m ≤ (4057 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0447

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0448
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (4057 / 10240) (8117 / 20480) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (4057 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (4057 / 5120) (8117 / 10240) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-8117 / 10240) (-4057 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2123 / 10240) (1063 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2123 / 10240) (1063 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (4057 / 2560) (8117 / 5120) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-8117 / 5120) (-4057 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (2123 / 5120) (1063 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (2123 / 5120) (1063 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1063 / 5120)
  have hx9 : Bounds (6183 / 5120) (6183 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1063 / 5120)
  have hx10 : Bounds (6183 / 5120) (6183 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (188649151 / 1000000000) (2947643 / 15625000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (113907978577 / 500000000000) (227815958363 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1063 / 5120)
  have hx13 : Bounds (-1063 / 5120) (-1063 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (4057 / 5120) (4057 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1063 / 5120)
  have hx15 : Bounds (4057 / 5120) (4057 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(1063 / 5120)
  have hx16 : Bounds (-1063 / 5120) (-1063 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (4057 / 5120) (4057 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1063 / 5120)
  have hx18 : Bounds (4057 / 5120) (4057 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-46542131 / 200000000) (-116355327 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-46098980827 / 250000000000) (-36879184503 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (21710016923 / 500000000000) (5427504481 / 125000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (21710016923 / 1000000000000) (5427504481 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (21710016923 / 1000000000000) (5427504481 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-5427504481 / 250000000000) (-21710016923 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (167859290519 / 250000000000) (671437164077 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (167859290519 / 250000000000) (671437164077 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1063 / 5120)
  have hx28 : Bounds (167859290519 / 250000000000) (671437164077 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2123 / 10240)
  have hx30 : Bounds (12363 / 10240) (12363 / 10240) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 10240) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2123 / 10240)
  have hx31 : Bounds (12363 / 10240) (12363 / 10240) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 10240) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (188406521 / 1000000000) (94203261 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (227467755773 / 1000000000000) (113733878491 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2123 / 10240)
  have hx34 : Bounds (-2123 / 10240) (-2123 / 10240) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 10240) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (8117 / 10240) (8117 / 10240) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2123 / 10240)
  have hx36 : Bounds (8117 / 10240) (8117 / 10240) x36 := by
    exact hx35
  let x37 : ℝ := -(2123 / 10240)
  have hx37 : Bounds (-2123 / 10240) (-2123 / 10240) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 10240) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (8117 / 10240) (8117 / 10240) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2123 / 10240)
  have hx39 : Bounds (8117 / 10240) (8117 / 10240) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-453791 / 1953125) (-232340991 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-3683421547 / 20000000000) (-184171076557 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (43296678423 / 1000000000000) (1731867217 / 40000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (21648339211 / 1000000000000) (21648340213 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (21648339211 / 1000000000000) (21648340213 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-21648340213 / 1000000000000) (-21648339211 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (671498839787 / 1000000000000) (671498841789 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (671498839787 / 1000000000000) (671498841789 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2123 / 10240)
  have hx49 : Bounds (671498839787 / 1000000000000) (671498841789 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (167859290519 / 250000000000) (671498841789 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1063 / 2560)
  have hx52 : Bounds (3623 / 2560) (3623 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1063 / 2560)
  have hx53 : Bounds (3623 / 2560) (3623 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1063 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (347295153 / 1000000000) (173647577 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (122876009699 / 250000000000) (122876010053 / 250000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1063 / 2560)
  have hx56 : Bounds (-1063 / 2560) (-1063 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1497 / 2560) (1497 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1063 / 2560)
  have hx58 : Bounds (1497 / 2560) (1497 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(1063 / 2560)
  have hx59 : Bounds (-1063 / 2560) (-1063 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1063 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1497 / 2560) (1497 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1063 / 2560)
  have hx61 : Bounds (1497 / 2560) (1497 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-268272077 / 500000000) (-536544153 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-156876288777 / 500000000000) (-313752576969 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (88875730621 / 500000000000) (177751463243 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (88875730621 / 1000000000000) (44437865811 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (88875730621 / 1000000000000) (44437865811 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-44437865811 / 500000000000) (-88875730621 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (302135724189 / 500000000000) (604271450379 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (302135724189 / 500000000000) (604271450379 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1063 / 2560)
  have hx71 : Bounds (302135724189 / 500000000000) (604271450379 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2123 / 5120)
  have hx73 : Bounds (7243 / 5120) (7243 / 5120) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 5120) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2123 / 5120)
  have hx74 : Bounds (7243 / 5120) (7243 / 5120) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 5120) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (173440523 / 500000000) (346881047 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (245357364861 / 500000000000) (490714731137 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2123 / 5120)
  have hx77 : Bounds (-2123 / 5120) (-2123 / 5120) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 5120) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2997 / 5120) (2997 / 5120) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2123 / 5120)
  have hx79 : Bounds (2997 / 5120) (2997 / 5120) x79 := by
    exact hx78
  let x80 : ℝ := -(2123 / 5120)
  have hx80 : Bounds (-2123 / 5120) (-2123 / 5120) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 5120) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2997 / 5120) (2997 / 5120) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2123 / 5120)
  have hx82 : Bounds (2997 / 5120) (2997 / 5120) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-535542651 / 1000000000) (-10710853 / 20000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-313480727549 / 1000000000000) (-156740363481 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (177234002173 / 1000000000000) (7089360167 / 40000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (44308500543 / 500000000000) (11077125261 / 125000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (44308500543 / 500000000000) (11077125261 / 125000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-11077125261 / 125000000000) (-44308500543 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (75566272239 / 125000000000) (302265089957 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (75566272239 / 125000000000) (302265089957 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2123 / 5120)
  have hx92 : Bounds (75566272239 / 125000000000) (302265089957 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (302135724189 / 500000000000) (302265089957 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (648709314189 / 500000000000) (648838680457 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (648709314189 / 1000000000000) (648838680457 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (648709314189 / 1000000000000) (648838680457 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(147733 / 500000)
  have hx100 : Bounds (647733 / 500000) (647733 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((147733 / 500000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(147733 / 500000)
  have hx101 : Bounds (647733 / 500000) (647733 / 500000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((147733 / 500000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (10354819 / 40000000) (64717619 / 250000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (167678949383 / 500000000000) (167678950031 / 500000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(147733 / 500000)
  have hx104 : Bounds (-147733 / 500000) (-147733 / 500000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((147733 / 500000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (352267 / 500000) (352267 / 500000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(147733 / 500000)
  have hx106 : Bounds (352267 / 500000) (352267 / 500000) x106 := by
    exact hx105
  let x107 : ℝ := -(147733 / 500000)
  have hx107 : Bounds (-147733 / 500000) (-147733 / 500000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((147733 / 500000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (352267 / 500000) (352267 / 500000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(147733 / 500000)
  have hx109 : Bounds (352267 / 500000) (352267 / 500000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-5472167 / 15625000) (-350218687 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-61685243283 / 250000000000) (-123370486213 / 500000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (44308462817 / 500000000000) (22154231909 / 250000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (44308462817 / 1000000000000) (22154231909 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (44308462817 / 1000000000000) (22154231909 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-22154231909 / 500000000000) (-44308462817 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (324419358091 / 500000000000) (648838718183 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (324419358091 / 500000000000) (648838718183 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (147733 / 500000)
  have hx119 : Bounds (324419358091 / 500000000000) (648838718183 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(295891 / 1000000)
  have hx121 : Bounds (1295891 / 1000000) (1295891 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((295891 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(295891 / 1000000)
  have hx122 : Bounds (1295891 / 1000000) (1295891 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((295891 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (259198489 / 1000000000) (25919849 / 100000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (83973247277 / 250000000000) (67178598081 / 200000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(295891 / 1000000)
  have hx125 : Bounds (-295891 / 1000000) (-295891 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((295891 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (704109 / 1000000) (704109 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(295891 / 1000000)
  have hx127 : Bounds (704109 / 1000000) (704109 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(295891 / 1000000)
  have hx128 : Bounds (-295891 / 1000000) (-295891 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((295891 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (704109 / 1000000) (704109 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(295891 / 1000000)
  have hx130 : Bounds (704109 / 1000000) (704109 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-175411053 / 500000000) (-70164421 / 200000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-123508501117 / 500000000000) (-247017001529 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (44437993437 / 500000000000) (22218997219 / 250000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (44437993437 / 1000000000000) (22218997219 / 500000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (44437993437 / 1000000000000) (22218997219 / 500000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-22218997219 / 500000000000) (-44437993437 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (324354592781 / 500000000000) (648709187563 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (324354592781 / 500000000000) (648709187563 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (295891 / 1000000)
  have hx140 : Bounds (324354592781 / 500000000000) (648709187563 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (147733 / 500000) (295891 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (295891 / 1000000) ≤ (648709187563 / 1000000000000) := hx140.2
      have h2 : (648709314189 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (648838680457 / 1000000000000) := hx98.2
      have h2 : (324419358091 / 500000000000) ≤ biasE (147733 / 500000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (4816556914393 / 1000000000000) (4823363165333 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (195284083293 / 62500000000) (78239614789 / 25000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (195284083293 / 62500000000) (78239614789 / 25000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(214101 / 1000000)
  have hx145 : Bounds (1214101 / 1000000) (1214101 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((214101 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(214101 / 1000000)
  have hx146 : Bounds (1214101 / 1000000) (1214101 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((214101 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (38800777 / 200000000) (97001943 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (117770155391 / 500000000000) (235540311997 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(214101 / 1000000)
  have hx149 : Bounds (-214101 / 1000000) (-214101 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((214101 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (785899 / 1000000) (785899 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(214101 / 1000000)
  have hx151 : Bounds (785899 / 1000000) (785899 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(214101 / 1000000)
  have hx152 : Bounds (-214101 / 1000000) (-214101 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((214101 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (785899 / 1000000) (785899 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(214101 / 1000000)
  have hx154 : Bounds (785899 / 1000000) (785899 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-120463497 / 500000000) (-240926993 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-94672141829 / 500000000000) (-189344282871 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (11549006781 / 250000000000) (23098014563 / 500000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (11549006781 / 500000000000) (23098014563 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (11549006781 / 500000000000) (23098014563 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-23098014563 / 1000000000000) (-11549006781 / 500000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (670049165437 / 1000000000000) (335024583719 / 500000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (670049165437 / 1000000000000) (335024583719 / 500000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (214101 / 1000000)
  have hx164 : Bounds (670049165437 / 1000000000000) (335024583719 / 500000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(8577 / 40000)
  have hx166 : Bounds (48577 / 40000) (48577 / 40000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((8577 / 40000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(8577 / 40000)
  have hx167 : Bounds (48577 / 40000) (48577 / 40000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((8577 / 40000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (194270713 / 1000000000) (97135357 / 500000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (47185442127 / 200000000000) (4718544237 / 20000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(8577 / 40000)
  have hx170 : Bounds (-8577 / 40000) (-8577 / 40000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((8577 / 40000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (31423 / 40000) (31423 / 40000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(8577 / 40000)
  have hx172 : Bounds (31423 / 40000) (31423 / 40000) x172 := by
    exact hx171
  let x173 : ℝ := -(8577 / 40000)
  have hx173 : Bounds (-8577 / 40000) (-8577 / 40000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((8577 / 40000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (31423 / 40000) (31423 / 40000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(8577 / 40000)
  have hx175 : Bounds (31423 / 40000) (31423 / 40000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-120669673 / 500000000) (-48267869 / 200000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-94795078367 / 500000000000) (-47397538987 / 250000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (46337053901 / 1000000000000) (23168527951 / 500000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (463370539 / 20000000000) (23168527951 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (463370539 / 20000000000) (23168527951 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-23168527951 / 1000000000000) (-463370539 / 20000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (669978652049 / 1000000000000) (13399573081 / 20000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (669978652049 / 1000000000000) (13399573081 / 20000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (8577 / 40000)
  have hx185 : Bounds (669978652049 / 1000000000000) (13399573081 / 20000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(214101 / 1000000)
  have hx186 : Bounds (668968280273 / 1000000000000) (335023595319 / 500000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((214101 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(8577 / 40000)
  have hx187 : Bounds (669980632961 / 1000000000000) (335530588023 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((8577 / 40000) : ℝ)) <;> norm_num
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
  have hc : Bounds (214101 / 1000000) (8577 / 40000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (214101 / 1000000) ≤ (335023595319 / 500000000000) := hx186.2
      have h2 : (670049165437 / 1000000000000) ≤ biasE (214101 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (8577 / 40000) ≤ (13399573081 / 20000000000) := hx185.2
      have h2 : (669980632961 / 1000000000000) ≤ x143 * (8577 / 40000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (647733 / 500000) (1295891 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-295891 / 1000000) (-147733 / 500000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (704109 / 1000000) (352267 / 500000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (704109 / 1000000) (352267 / 500000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1419377915047 / 1000000000000) (142023465117 / 100000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (919377915047 / 500000000000) (92023465117 / 50000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (919377915047 / 500000000000) (92023465117 / 50000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (609089163 / 1000000000) (122004119 / 200000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (609089163 / 2000000000) (122004119 / 400000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (609089163 / 2000000000) (122004119 / 400000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1214101 / 1000000) (48577 / 40000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-8577 / 40000) (-214101 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (31423 / 40000) (785899 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (31423 / 40000) (785899 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1272428136439 / 1000000000000) (636476466283 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (772428136439 / 500000000000) (386476466283 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (772428136439 / 500000000000) (386476466283 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (217465439 / 500000000) (21780503 / 50000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (217465439 / 1000000000) (21780503 / 100000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (217465439 / 1000000000) (21780503 / 100000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (167859290519 / 125000000000) (671498841789 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (648709314189 / 500000000000) (648838680457 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-648838680457 / 500000000000) (-648709314189 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (22598481619 / 500000000000) (56973819 / 1250000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (22598481619 / 500000000000) (56973819 / 1250000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (89982569317 / 1000000000000) (45124900969 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-45124900969 / 500000000000) (-89982569317 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-450528387 / 10000000000) (-44403514117 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-450528387 / 10000000000) (-44403514117 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (9017170449 / 200000000000) (5652508469 / 125000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (6602709 / 200000000000) (163310727 / 200000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (4057 / 10240) (8117 / 20480) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (4057 / 10240) ≤ m → m ≤ (8117 / 20480) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0448

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0449
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (8117 / 20480) (203 / 512) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (8117 / 20480) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (8117 / 10240) (203 / 256) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-203 / 256) (-8117 / 10240) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (53 / 256) (2123 / 10240) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (53 / 256) (2123 / 10240) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (8117 / 5120) (203 / 128) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-203 / 128) (-8117 / 5120) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (53 / 128) (2123 / 5120) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (53 / 128) (2123 / 5120) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2123 / 10240)
  have hx9 : Bounds (12363 / 10240) (12363 / 10240) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 10240) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2123 / 10240)
  have hx10 : Bounds (12363 / 10240) (12363 / 10240) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 10240) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (188406521 / 1000000000) (94203261 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (227467755773 / 1000000000000) (113733878491 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2123 / 10240)
  have hx13 : Bounds (-2123 / 10240) (-2123 / 10240) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 10240) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (8117 / 10240) (8117 / 10240) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2123 / 10240)
  have hx15 : Bounds (8117 / 10240) (8117 / 10240) x15 := by
    exact hx14
  let x16 : ℝ := -(2123 / 10240)
  have hx16 : Bounds (-2123 / 10240) (-2123 / 10240) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 10240) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (8117 / 10240) (8117 / 10240) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2123 / 10240)
  have hx18 : Bounds (8117 / 10240) (8117 / 10240) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-453791 / 1953125) (-232340991 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-3683421547 / 20000000000) (-184171076557 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (43296678423 / 1000000000000) (1731867217 / 40000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (21648339211 / 1000000000000) (21648340213 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (21648339211 / 1000000000000) (21648340213 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-21648340213 / 1000000000000) (-21648339211 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (671498839787 / 1000000000000) (671498841789 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (671498839787 / 1000000000000) (671498841789 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2123 / 10240)
  have hx28 : Bounds (671498839787 / 1000000000000) (671498841789 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(53 / 256)
  have hx30 : Bounds (309 / 256) (309 / 256) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 256) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(53 / 256)
  have hx31 : Bounds (309 / 256) (309 / 256) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 256) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (23520479 / 125000000) (188163833 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (227119625343 / 1000000000000) (227119626551 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(53 / 256)
  have hx34 : Bounds (-53 / 256) (-53 / 256) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 256) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (203 / 256) (203 / 256) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(53 / 256)
  have hx36 : Bounds (203 / 256) (203 / 256) x36 := by
    exact hx35
  let x37 : ℝ := -(53 / 256)
  have hx37 : Bounds (-53 / 256) (-53 / 256) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 256) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (203 / 256) (203 / 256) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(53 / 256)
  have hx39 : Bounds (203 / 256) (203 / 256) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-115985733 / 500000000) (-46394293 / 200000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-18394612343 / 100000000000) (-45986530659 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (43173501913 / 1000000000000) (8634700783 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (5396687739 / 250000000000) (10793375979 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (5396687739 / 250000000000) (10793375979 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-10793375979 / 500000000000) (-5396687739 / 250000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (335780214021 / 500000000000) (167890107511 / 250000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (335780214021 / 500000000000) (167890107511 / 250000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (53 / 256)
  have hx49 : Bounds (335780214021 / 500000000000) (167890107511 / 250000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (671498839787 / 1000000000000) (167890107511 / 250000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2123 / 5120)
  have hx52 : Bounds (7243 / 5120) (7243 / 5120) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 5120) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2123 / 5120)
  have hx53 : Bounds (7243 / 5120) (7243 / 5120) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2123 / 5120) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (173440523 / 500000000) (346881047 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (245357364861 / 500000000000) (490714731137 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2123 / 5120)
  have hx56 : Bounds (-2123 / 5120) (-2123 / 5120) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 5120) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2997 / 5120) (2997 / 5120) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2123 / 5120)
  have hx58 : Bounds (2997 / 5120) (2997 / 5120) x58 := by
    exact hx57
  let x59 : ℝ := -(2123 / 5120)
  have hx59 : Bounds (-2123 / 5120) (-2123 / 5120) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2123 / 5120) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2997 / 5120) (2997 / 5120) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2123 / 5120)
  have hx61 : Bounds (2997 / 5120) (2997 / 5120) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-535542651 / 1000000000) (-10710853 / 20000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-313480727549 / 1000000000000) (-156740363481 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (177234002173 / 1000000000000) (7089360167 / 40000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (44308500543 / 500000000000) (11077125261 / 125000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (44308500543 / 500000000000) (11077125261 / 125000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-11077125261 / 125000000000) (-44308500543 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (75566272239 / 125000000000) (302265089957 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (75566272239 / 125000000000) (302265089957 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2123 / 5120)
  have hx71 : Bounds (75566272239 / 125000000000) (302265089957 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(53 / 128)
  have hx73 : Bounds (181 / 128) (181 / 128) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 128) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(53 / 128)
  have hx74 : Bounds (181 / 128) (181 / 128) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 128) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (346466767 / 1000000000) (21654173 / 62500000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (48992566271 / 100000000000) (3919405313 / 8000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(53 / 128)
  have hx77 : Bounds (-53 / 128) (-53 / 128) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 128) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (75 / 128) (75 / 128) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(53 / 128)
  have hx79 : Bounds (75 / 128) (75 / 128) x79 := by
    exact hx78
  let x80 : ℝ := -(53 / 128)
  have hx80 : Bounds (-53 / 128) (-53 / 128) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 128) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (75 / 128) (75 / 128) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(53 / 128)
  have hx82 : Bounds (75 / 128) (75 / 128) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-534542151 / 1000000000) (-10690843 / 20000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-156604145801 / 500000000000) (-62641658203 / 200000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (44179342777 / 250000000000) (17671737311 / 100000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (44179342777 / 500000000000) (17671737311 / 200000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (44179342777 / 500000000000) (17671737311 / 200000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-17671737311 / 200000000000) (-44179342777 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (120957698689 / 200000000000) (302394247723 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (120957698689 / 200000000000) (302394247723 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (53 / 128)
  have hx92 : Bounds (120957698689 / 200000000000) (302394247723 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (75566272239 / 125000000000) (302394247723 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (162209669739 / 125000000000) (648967838223 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (162209669739 / 250000000000) (648967838223 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (162209669739 / 250000000000) (648967838223 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(295041 / 1000000)
  have hx100 : Bounds (1295041 / 1000000) (1295041 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((295041 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(295041 / 1000000)
  have hx101 : Bounds (1295041 / 1000000) (1295041 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((295041 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (129271177 / 500000000) (51708471 / 200000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (167411474333 / 500000000000) (167411474981 / 500000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(295041 / 1000000)
  have hx104 : Bounds (-295041 / 1000000) (-295041 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((295041 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (704959 / 1000000) (704959 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(295041 / 1000000)
  have hx106 : Bounds (704959 / 1000000) (704959 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(295041 / 1000000)
  have hx107 : Bounds (-295041 / 1000000) (-295041 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((295041 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (704959 / 1000000) (704959 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(295041 / 1000000)
  have hx109 : Bounds (704959 / 1000000) (704959 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-174807817 / 500000000) (-349615633 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-24646468773 / 100000000000) (-15404042939 / 62500000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (11044782617 / 125000000000) (44179131469 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (11044782617 / 250000000000) (44179131469 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (11044782617 / 250000000000) (44179131469 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-44179131469 / 1000000000000) (-11044782617 / 250000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (648968048531 / 1000000000000) (162242012633 / 250000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (648968048531 / 1000000000000) (162242012633 / 250000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (295041 / 1000000)
  have hx119 : Bounds (648968048531 / 1000000000000) (162242012633 / 250000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(295467 / 1000000)
  have hx121 : Bounds (1295467 / 1000000) (1295467 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((295467 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(295467 / 1000000)
  have hx122 : Bounds (1295467 / 1000000) (1295467 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((295467 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (258871247 / 1000000000) (16179453 / 62500000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (335359157737 / 1000000000000) (335359159033 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(295467 / 1000000)
  have hx125 : Bounds (-295467 / 1000000) (-295467 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((295467 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (704533 / 1000000) (704533 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(295467 / 1000000)
  have hx127 : Bounds (704533 / 1000000) (704533 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(295467 / 1000000)
  have hx128 : Bounds (-295467 / 1000000) (-295467 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((295467 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (704533 / 1000000) (704533 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(295467 / 1000000)
  have hx130 : Bounds (704533 / 1000000) (704533 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-87555027 / 250000000) (-350220107 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-4934832467 / 20000000000) (-49348324529 / 200000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (88617534387 / 1000000000000) (22154384097 / 250000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (44308767193 / 1000000000000) (22154384097 / 500000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (44308767193 / 1000000000000) (22154384097 / 500000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-22154384097 / 500000000000) (-44308767193 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (324419205903 / 500000000000) (648838413807 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (324419205903 / 500000000000) (648838413807 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (295467 / 1000000)
  have hx140 : Bounds (324419205903 / 500000000000) (648838413807 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (295041 / 1000000) (295467 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (295467 / 1000000) ≤ (648838413807 / 1000000000000) := hx140.2
      have h2 : (162209669739 / 250000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (648967838223 / 1000000000000) := hx98.2
      have h2 : (648968048531 / 1000000000000) ≤ biasE (295041 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (1205840791333 / 250000000000) (2415094339623 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (3129584584319 / 1000000000000) (156731855269 / 50000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (3129584584319 / 1000000000000) (156731855269 / 50000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(106889 / 500000)
  have hx145 : Bounds (606889 / 500000) (606889 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((106889 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(106889 / 500000)
  have hx146 : Bounds (606889 / 500000) (606889 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((106889 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (193737809 / 1000000000) (19373781 / 100000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (58788672583 / 250000000000) (235154691547 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(106889 / 500000)
  have hx149 : Bounds (-106889 / 500000) (-106889 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((106889 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (393111 / 500000) (393111 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(106889 / 500000)
  have hx151 : Bounds (393111 / 500000) (393111 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(106889 / 500000)
  have hx152 : Bounds (-106889 / 500000) (-106889 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((106889 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (393111 / 500000) (393111 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(106889 / 500000)
  have hx154 : Bounds (393111 / 500000) (393111 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-60129021 / 250000000) (-240516083 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-37819807319 / 200000000000) (-5909344869 / 31250000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (46055653737 / 1000000000000) (46055655739 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (5756956717 / 250000000000) (2302782787 / 100000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (5756956717 / 250000000000) (2302782787 / 100000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-2302782787 / 100000000000) (-5756956717 / 250000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (67011935213 / 100000000000) (167529838533 / 250000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (67011935213 / 100000000000) (167529838533 / 250000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (106889 / 500000)
  have hx164 : Bounds (67011935213 / 100000000000) (167529838533 / 250000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(107051 / 500000)
  have hx166 : Bounds (607051 / 500000) (607051 / 500000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((107051 / 500000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(107051 / 500000)
  have hx167 : Bounds (607051 / 500000) (607051 / 500000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((107051 / 500000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (48501177 / 250000000) (194004709 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (29442687999 / 125000000000) (235541505207 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(107051 / 500000)
  have hx170 : Bounds (-107051 / 500000) (-107051 / 500000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((107051 / 500000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (392949 / 500000) (392949 / 500000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(107051 / 500000)
  have hx172 : Bounds (392949 / 500000) (392949 / 500000) x172 := by
    exact hx171
  let x173 : ℝ := -(107051 / 500000)
  have hx173 : Bounds (-107051 / 500000) (-107051 / 500000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((107051 / 500000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (392949 / 500000) (392949 / 500000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(107051 / 500000)
  have hx175 : Bounds (392949 / 500000) (392949 / 500000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-120464133 / 500000000) (-48185653 / 200000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-189345042393 / 1000000000000) (-94672520803 / 500000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (46196461599 / 1000000000000) (46196463601 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (23098230799 / 1000000000000) (23098231801 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (23098230799 / 1000000000000) (23098231801 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-23098231801 / 1000000000000) (-23098230799 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (670048948199 / 1000000000000) (670048950201 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (670048948199 / 1000000000000) (670048950201 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (107051 / 500000)
  have hx185 : Bounds (670048948199 / 1000000000000) (670048950201 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(106889 / 500000)
  have hx186 : Bounds (334518166633 / 500000000000) (335058225557 / 500000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((106889 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(107051 / 500000)
  have hx187 : Bounds (670050318671 / 1000000000000) (671132073537 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((107051 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (106889 / 500000) (107051 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (106889 / 500000) ≤ (335058225557 / 500000000000) := hx186.2
      have h2 : (67011935213 / 100000000000) ≤ biasE (106889 / 500000) := hx164.1
      linarith
    · have h1 : biasE (107051 / 500000) ≤ (670048950201 / 1000000000000) := hx185.2
      have h2 : (670050318671 / 1000000000000) ≤ x143 * (107051 / 500000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1295041 / 1000000) (1295467 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-295467 / 1000000) (-295041 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (704533 / 1000000) (704959 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (704533 / 1000000) (704959 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (141852221193 / 100000000000) (354844982421 / 250000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (91852221193 / 50000000000) (229844982421 / 125000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (91852221193 / 50000000000) (229844982421 / 125000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (152039497 / 250000000) (121818271 / 200000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (152039497 / 500000000) (121818271 / 400000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (152039497 / 500000000) (121818271 / 400000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (606889 / 500000) (607051 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-107051 / 500000) (-106889 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (392949 / 500000) (393111 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (392949 / 500000) (393111 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1271905390589 / 1000000000000) (318107438879 / 250000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (771905390589 / 500000000000) (193107438879 / 125000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (771905390589 / 500000000000) (193107438879 / 125000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (434253893 / 1000000000) (17397319 / 40000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (434253893 / 2000000000) (17397319 / 80000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (434253893 / 2000000000) (17397319 / 80000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (671498839787 / 500000000000) (167890107511 / 125000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (162209669739 / 125000000000) (648967838223 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-648967838223 / 500000000000) (-162209669739 / 125000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (5632750391 / 125000000000) (1420109443 / 31250000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (5632750391 / 125000000000) (1420109443 / 31250000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (22428942617 / 250000000000) (44991598847 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-44991598847 / 500000000000) (-22428942617 / 250000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-22460597283 / 500000000000) (-11068067073 / 250000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-22460597283 / 500000000000) (-11068067073 / 250000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (22476031571 / 500000000000) (22543034813 / 500000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (964643 / 31250000000) (406900667 / 500000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (8117 / 20480) (203 / 512) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (8117 / 20480) ≤ m → m ≤ (203 / 512) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0449

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0450
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (203 / 512) (8123 / 20480) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (203 / 512) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (203 / 256) (8123 / 10240) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-8123 / 10240) (-203 / 256) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2117 / 10240) (53 / 256) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2117 / 10240) (53 / 256) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (203 / 128) (8123 / 5120) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-8123 / 5120) (-203 / 128) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (2117 / 5120) (53 / 128) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (2117 / 5120) (53 / 128) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(53 / 256)
  have hx9 : Bounds (309 / 256) (309 / 256) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 256) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(53 / 256)
  have hx10 : Bounds (309 / 256) (309 / 256) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 256) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (23520479 / 125000000) (188163833 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (227119625343 / 1000000000000) (227119626551 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(53 / 256)
  have hx13 : Bounds (-53 / 256) (-53 / 256) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 256) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (203 / 256) (203 / 256) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(53 / 256)
  have hx15 : Bounds (203 / 256) (203 / 256) x15 := by
    exact hx14
  let x16 : ℝ := -(53 / 256)
  have hx16 : Bounds (-53 / 256) (-53 / 256) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 256) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (203 / 256) (203 / 256) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(53 / 256)
  have hx18 : Bounds (203 / 256) (203 / 256) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-115985733 / 500000000) (-46394293 / 200000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-18394612343 / 100000000000) (-45986530659 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (43173501913 / 1000000000000) (8634700783 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (5396687739 / 250000000000) (10793375979 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (5396687739 / 250000000000) (10793375979 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-10793375979 / 500000000000) (-5396687739 / 250000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (335780214021 / 500000000000) (167890107511 / 250000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (335780214021 / 500000000000) (167890107511 / 250000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (53 / 256)
  have hx28 : Bounds (335780214021 / 500000000000) (167890107511 / 250000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2117 / 10240)
  have hx30 : Bounds (12357 / 10240) (12357 / 10240) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2117 / 10240) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2117 / 10240)
  have hx31 : Bounds (12357 / 10240) (12357 / 10240) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2117 / 10240) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (46980271 / 250000000) (37584217 / 200000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (56692891479 / 250000000000) (56692891781 / 250000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2117 / 10240)
  have hx34 : Bounds (-2117 / 10240) (-2117 / 10240) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2117 / 10240) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (8123 / 10240) (8123 / 10240) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2117 / 10240)
  have hx36 : Bounds (8123 / 10240) (8123 / 10240) x36 := by
    exact hx35
  let x37 : ℝ := -(2117 / 10240)
  have hx37 : Bounds (-2117 / 10240) (-2117 / 10240) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2117 / 10240) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (8123 / 10240) (8123 / 10240) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2117 / 10240)
  have hx39 : Bounds (8123 / 10240) (8123 / 10240) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-57900519 / 250000000) (-9264083 / 40000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-91860530437 / 500000000000) (-2296513251 / 12500000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (21525252521 / 500000000000) (10762626761 / 250000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (21525252521 / 1000000000000) (10762626761 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (21525252521 / 1000000000000) (10762626761 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-10762626761 / 500000000000) (-21525252521 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (335810963239 / 500000000000) (671621928479 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (335810963239 / 500000000000) (671621928479 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2117 / 10240)
  have hx49 : Bounds (335810963239 / 500000000000) (671621928479 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (335780214021 / 500000000000) (671621928479 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(53 / 128)
  have hx52 : Bounds (181 / 128) (181 / 128) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 128) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(53 / 128)
  have hx53 : Bounds (181 / 128) (181 / 128) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((53 / 128) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (346466767 / 1000000000) (21654173 / 62500000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (48992566271 / 100000000000) (3919405313 / 8000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(53 / 128)
  have hx56 : Bounds (-53 / 128) (-53 / 128) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 128) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (75 / 128) (75 / 128) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(53 / 128)
  have hx58 : Bounds (75 / 128) (75 / 128) x58 := by
    exact hx57
  let x59 : ℝ := -(53 / 128)
  have hx59 : Bounds (-53 / 128) (-53 / 128) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((53 / 128) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (75 / 128) (75 / 128) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(53 / 128)
  have hx61 : Bounds (75 / 128) (75 / 128) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-534542151 / 1000000000) (-10690843 / 20000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-156604145801 / 500000000000) (-62641658203 / 200000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (44179342777 / 250000000000) (17671737311 / 100000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (44179342777 / 500000000000) (17671737311 / 200000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (44179342777 / 500000000000) (17671737311 / 200000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-17671737311 / 200000000000) (-44179342777 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (120957698689 / 200000000000) (302394247723 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (120957698689 / 200000000000) (302394247723 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (53 / 128)
  have hx71 : Bounds (120957698689 / 200000000000) (302394247723 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2117 / 5120)
  have hx73 : Bounds (7237 / 5120) (7237 / 5120) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2117 / 5120) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2117 / 5120)
  have hx74 : Bounds (7237 / 5120) (7237 / 5120) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2117 / 5120) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (86513079 / 250000000) (346052317 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (30571052379 / 62500000000) (489136839479 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2117 / 5120)
  have hx77 : Bounds (-2117 / 5120) (-2117 / 5120) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2117 / 5120) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (3003 / 5120) (3003 / 5120) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2117 / 5120)
  have hx79 : Bounds (3003 / 5120) (3003 / 5120) x79 := by
    exact hx78
  let x80 : ℝ := -(2117 / 5120)
  have hx80 : Bounds (-2117 / 5120) (-2117 / 5120) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2117 / 5120) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (3003 / 5120) (3003 / 5120) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2117 / 5120)
  have hx82 : Bounds (3003 / 5120) (3003 / 5120) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-533542651 / 1000000000) (-10670853 / 20000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-156467634859 / 500000000000) (-31293526913 / 100000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (88100784173 / 500000000000) (176201570349 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (88100784173 / 1000000000000) (3524031407 / 40000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (88100784173 / 1000000000000) (3524031407 / 40000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-3524031407 / 40000000000) (-88100784173 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (24201855793 / 40000000000) (605046396827 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (24201855793 / 40000000000) (605046396827 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2117 / 5120)
  have hx92 : Bounds (24201855793 / 40000000000) (605046396827 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (120957698689 / 200000000000) (605046396827 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (259587134689 / 200000000000) (1298193577827 / 1000000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (324483918361 / 500000000000) (324548394457 / 500000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (324483918361 / 500000000000) (324548394457 / 500000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(294617 / 1000000)
  have hx100 : Bounds (1294617 / 1000000) (1294617 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((294617 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(294617 / 1000000)
  have hx101 : Bounds (1294617 / 1000000) (1294617 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((294617 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (129107449 / 500000000) (258214899 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (83572349151 / 250000000000) (334289397899 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(294617 / 1000000)
  have hx104 : Bounds (-294617 / 1000000) (-294617 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((294617 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (705383 / 1000000) (705383 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(294617 / 1000000)
  have hx106 : Bounds (705383 / 1000000) (705383 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(294617 / 1000000)
  have hx107 : Bounds (-294617 / 1000000) (-294617 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((294617 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (705383 / 1000000) (705383 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(294617 / 1000000)
  have hx109 : Bounds (705383 / 1000000) (705383 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-174507181 / 500000000) (-349014361 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-246188797711 / 1000000000000) (-49237759401 / 200000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (88100598893 / 1000000000000) (44050300447 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (22025149723 / 500000000000) (44050300447 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (22025149723 / 500000000000) (44050300447 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-44050300447 / 1000000000000) (-22025149723 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (649096879553 / 1000000000000) (324548440777 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (649096879553 / 1000000000000) (324548440777 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (294617 / 1000000)
  have hx119 : Bounds (649096879553 / 1000000000000) (324548440777 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(147521 / 500000)
  have hx121 : Bounds (647521 / 500000) (647521 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((147521 / 500000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(147521 / 500000)
  have hx122 : Bounds (647521 / 500000) (647521 / 500000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((147521 / 500000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (258543127 / 1000000000) (32317891 / 125000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (83706052069 / 250000000000) (83706052393 / 250000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(147521 / 500000)
  have hx125 : Bounds (-147521 / 500000) (-147521 / 500000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((147521 / 500000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (352479 / 500000) (352479 / 500000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(147521 / 500000)
  have hx127 : Bounds (352479 / 500000) (352479 / 500000) x127 := by
    exact hx126
  let x128 : ℝ := -(147521 / 500000)
  have hx128 : Bounds (-147521 / 500000) (-147521 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((147521 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (352479 / 500000) (352479 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(147521 / 500000)
  have hx130 : Bounds (352479 / 500000) (352479 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-349617053 / 1000000000) (-87404263 / 250000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-246465338449 / 1000000000000) (-246465337743 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (88358869827 / 1000000000000) (88358871829 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (44179434913 / 1000000000000) (8835887183 / 200000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (44179434913 / 1000000000000) (8835887183 / 200000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-8835887183 / 200000000000) (-44179434913 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (129793548817 / 200000000000) (648967746087 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (129793548817 / 200000000000) (648967746087 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (147521 / 500000)
  have hx140 : Bounds (129793548817 / 200000000000) (648967746087 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (294617 / 1000000) (147521 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (147521 / 500000) ≤ (648967746087 / 1000000000000) := hx140.2
      have h2 : (324483918361 / 500000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (324548394457 / 500000000000) := hx98.2
      have h2 : (649096879553 / 1000000000000) ≤ biasE (294617 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (966037735849 / 200000000000) (2418516769013 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (195914818633 / 62500000000) (3139702937403 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (195914818633 / 62500000000) (3139702937403 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(13341 / 62500)
  have hx145 : Bounds (75841 / 62500) (75841 / 62500) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((13341 / 62500) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(13341 / 62500)
  have hx146 : Bounds (75841 / 62500) (75841 / 62500) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((13341 / 62500) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (96736243 / 500000000) (193472487 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (234770348971 / 1000000000000) (117385175093 / 500000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(13341 / 62500)
  have hx149 : Bounds (-13341 / 62500) (-13341 / 62500) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((13341 / 62500) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (49159 / 62500) (49159 / 62500) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(13341 / 62500)
  have hx151 : Bounds (49159 / 62500) (49159 / 62500) x151 := by
    exact hx150
  let x152 : ℝ := -(13341 / 62500)
  have hx152 : Bounds (-13341 / 62500) (-13341 / 62500) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((13341 / 62500) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (49159 / 62500) (49159 / 62500) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(13341 / 62500)
  have hx154 : Bounds (49159 / 62500) (49159 / 62500) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-120053307 / 500000000) (-240106613 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-188854416603 / 1000000000000) (-37770883163 / 200000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (2869745773 / 62500000000) (45915934371 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (2869745773 / 125000000000) (11478983593 / 500000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (2869745773 / 125000000000) (11478983593 / 500000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-11478983593 / 500000000000) (-2869745773 / 125000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (335094606407 / 500000000000) (20943412963 / 31250000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (335094606407 / 500000000000) (20943412963 / 31250000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (13341 / 62500)
  have hx164 : Bounds (335094606407 / 500000000000) (20943412963 / 31250000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(213779 / 1000000)
  have hx166 : Bounds (1213779 / 1000000) (1213779 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((213779 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(213779 / 1000000)
  have hx167 : Bounds (1213779 / 1000000) (1213779 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((213779 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (193738633 / 1000000000) (96869317 / 500000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (3674310691 / 15625000000) (117577942719 / 500000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(213779 / 1000000)
  have hx170 : Bounds (-213779 / 1000000) (-213779 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((213779 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (786221 / 1000000) (786221 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(213779 / 1000000)
  have hx172 : Bounds (786221 / 1000000) (786221 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(213779 / 1000000)
  have hx173 : Bounds (-213779 / 1000000) (-213779 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((213779 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (786221 / 1000000) (786221 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(213779 / 1000000)
  have hx175 : Bounds (786221 / 1000000) (786221 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-60129339 / 250000000) (-48103471 / 200000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-23637474519 / 125000000000) (-37819959073 / 200000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (5757011009 / 125000000000) (46056090073 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (5757011009 / 250000000000) (23028045037 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (5757011009 / 250000000000) (23028045037 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-23028045037 / 1000000000000) (-5757011009 / 250000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (670119134963 / 1000000000000) (167529784241 / 250000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (670119134963 / 1000000000000) (167529784241 / 250000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (213779 / 1000000)
  have hx185 : Bounds (670119134963 / 1000000000000) (167529784241 / 250000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(13341 / 62500)
  have hx186 : Bounds (334553548209 / 500000000000) (670188430207 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((13341 / 62500) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(213779 / 1000000)
  have hx187 : Bounds (3350597921 / 5000000000) (41950159641 / 62500000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((213779 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (13341 / 62500) (213779 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (13341 / 62500) ≤ (670188430207 / 1000000000000) := hx186.2
      have h2 : (335094606407 / 500000000000) ≤ biasE (13341 / 62500) := hx164.1
      linarith
    · have h1 : biasE (213779 / 1000000) ≤ (167529784241 / 250000000000) := hx185.2
      have h2 : (3350597921 / 5000000000) ≤ x143 * (213779 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1294617 / 1000000) (647521 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-147521 / 500000) (-294617 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (352479 / 500000) (705383 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (352479 / 500000) (705383 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1417669549733 / 1000000000000) (1418524224139 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (917669549733 / 500000000000) (918524224139 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (917669549733 / 500000000000) (918524224139 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (607229259 / 1000000000) (30408009 / 50000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (607229259 / 2000000000) (30408009 / 100000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (607229259 / 2000000000) (30408009 / 100000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (75841 / 62500) (1213779 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-213779 / 1000000) (-13341 / 62500) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (786221 / 1000000) (49159 / 62500) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (786221 / 1000000) (49159 / 62500) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (635692345247 / 500000000000) (254381401667 / 200000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (385692345247 / 250000000000) (154381401667 / 100000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (385692345247 / 250000000000) (154381401667 / 100000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (4335791 / 10000000) (434255989 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (4335791 / 20000000) (434255989 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (4335791 / 20000000) (434255989 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (335780214021 / 250000000000) (671621928479 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (324483918361 / 250000000000) (324548394457 / 250000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-324548394457 / 250000000000) (-324483918361 / 250000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (2807954891 / 62500000000) (22654091757 / 500000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (2807954891 / 62500000000) (22654091757 / 500000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (89450031299 / 1000000000000) (44858198957 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-44858198957 / 500000000000) (-89450031299 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-22394559829 / 500000000000) (-8828369557 / 200000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-22394559829 / 500000000000) (-8828369557 / 200000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (44818698959 / 1000000000000) (2809517507 / 62500000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (29579301 / 1000000000000) (810432327 / 1000000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (203 / 512) (8123 / 20480) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (203 / 512) ≤ m → m ≤ (8123 / 20480) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0450

end


