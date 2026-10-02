-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0136__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0136__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:43:17.033382+00:00
-- url     : https://prove2.me/theorems/70c4b7ed-c240-45ee-986f-f5c81fa303d6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0136 (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0137, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0138, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0139, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0140, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0141, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0142).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0133Logs__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0139Logs__6

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1671 / 51200) (169 / 5120) m) :
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
  have hx0 : Bounds (1671 / 25600) (169 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-169 / 2560) (-1671 / 25600) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2391 / 2560) (23929 / 25600) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2391 / 2560) (23929 / 25600) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1671 / 12800) (169 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-169 / 1280) (-1671 / 12800) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1111 / 1280) (11129 / 12800) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (1111 / 1280) (11129 / 12800) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(23929 / 25600)
  have hx9 : Bounds (49529 / 25600) (49529 / 25600) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23929 / 25600) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(23929 / 25600)
  have hx10 : Bounds (49529 / 25600) (49529 / 25600) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23929 / 25600) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (131993201 / 200000000) (329983003 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (63842688011 / 50000000000) (319213440539 / 250000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(23929 / 25600)
  have hx13 : Bounds (-23929 / 25600) (-23929 / 25600) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23929 / 25600) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1671 / 25600) (1671 / 25600) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(23929 / 25600)
  have hx15 : Bounds (1671 / 25600) (1671 / 25600) x15 := by
    exact hx14
  let x16 : ℝ := -(23929 / 25600)
  have hx16 : Bounds (-23929 / 25600) (-23929 / 25600) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23929 / 25600) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1671 / 25600) (1671 / 25600) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(23929 / 25600)
  have hx18 : Bounds (1671 / 25600) (1671 / 25600) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-341146263 / 125000000) (-27291701 / 10000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-178142314211 / 1000000000000) (-178142313949 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1098711446009 / 1000000000000) (1098711448207 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (137338930751 / 250000000000) (68669465513 / 125000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (137338930751 / 250000000000) (68669465513 / 125000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-68669465513 / 125000000000) (-137338930751 / 250000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (17973931987 / 125000000000) (35947864499 / 250000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (17973931987 / 125000000000) (35947864499 / 250000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (23929 / 25600)
  have hx28 : Bounds (17973931987 / 125000000000) (35947864499 / 250000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2391 / 2560)
  have hx30 : Bounds (4951 / 2560) (4951 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2391 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2391 / 2560)
  have hx31 : Bounds (4951 / 2560) (4951 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2391 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (659582317 / 1000000000) (329791159 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (19931592111 / 15625000000) (1275621897039 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2391 / 2560)
  have hx34 : Bounds (-2391 / 2560) (-2391 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2391 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (169 / 2560) (169 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2391 / 2560)
  have hx36 : Bounds (169 / 2560) (169 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(2391 / 2560)
  have hx37 : Bounds (-2391 / 2560) (-2391 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2391 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (169 / 2560) (169 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2391 / 2560)
  have hx39 : Bounds (169 / 2560) (169 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-169866489 / 62500000) (-135893191 / 50000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-179421479007 / 1000000000000) (-89710739371 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1096200416097 / 1000000000000) (1096200418297 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (34256263003 / 62500000000) (548100209149 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (34256263003 / 62500000000) (548100209149 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-548100209149 / 1000000000000) (-34256263003 / 62500000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (145046970851 / 1000000000000) (18130871619 / 125000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (145046970851 / 1000000000000) (18130871619 / 125000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2391 / 2560)
  have hx49 : Bounds (145046970851 / 1000000000000) (18130871619 / 125000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (17973931987 / 125000000000) (18130871619 / 125000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(11129 / 12800)
  have hx52 : Bounds (23929 / 12800) (23929 / 12800) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11129 / 12800) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(11129 / 12800)
  have hx53 : Bounds (23929 / 12800) (23929 / 12800) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11129 / 12800) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (625645941 / 1000000000) (312822971 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (584807879773 / 500000000000) (146201970177 / 125000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(11129 / 12800)
  have hx56 : Bounds (-11129 / 12800) (-11129 / 12800) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11129 / 12800) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1671 / 12800) (1671 / 12800) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(11129 / 12800)
  have hx58 : Bounds (1671 / 12800) (1671 / 12800) x58 := by
    exact hx57
  let x59 : ℝ := -(11129 / 12800)
  have hx59 : Bounds (-11129 / 12800) (-11129 / 12800) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11129 / 12800) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1671 / 12800) (1671 / 12800) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(11129 / 12800)
  have hx61 : Bounds (1671 / 12800) (1671 / 12800) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2036022923 / 1000000000) (-50900573 / 25000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-265796430027 / 1000000000000) (-132898214817 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (903819329519 / 1000000000000) (451909665891 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (451909664759 / 1000000000000) (451909665891 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (451909664759 / 1000000000000) (451909665891 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-451909665891 / 1000000000000) (-451909664759 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (241237514109 / 1000000000000) (241237516241 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (241237514109 / 1000000000000) (241237516241 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (11129 / 12800)
  have hx71 : Bounds (241237514109 / 1000000000000) (241237516241 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1111 / 1280)
  have hx73 : Bounds (2391 / 1280) (2391 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1111 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1111 / 1280)
  have hx74 : Bounds (2391 / 1280) (2391 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1111 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (62485161 / 100000000) (624851611 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1167203280867 / 1000000000000) (72950205171 / 62500000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1111 / 1280)
  have hx77 : Bounds (-1111 / 1280) (-1111 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1111 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (169 / 1280) (169 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1111 / 1280)
  have hx79 : Bounds (169 / 1280) (169 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(1111 / 1280)
  have hx80 : Bounds (-1111 / 1280) (-1111 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1111 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (169 / 1280) (169 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1111 / 1280)
  have hx82 : Bounds (169 / 1280) (169 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2024716643 / 1000000000) (-12654479 / 6250000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-33415733659 / 125000000000) (-2138606951 / 8000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (179975482319 / 200000000000) (899877413861 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (449938705797 / 1000000000000) (449938706931 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (449938705797 / 1000000000000) (449938706931 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-449938706931 / 1000000000000) (-449938705797 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (243208473069 / 1000000000000) (243208475203 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (243208473069 / 1000000000000) (243208475203 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1111 / 1280)
  have hx92 : Bounds (243208473069 / 1000000000000) (243208475203 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (241237514109 / 1000000000000) (243208475203 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (60309378527 / 500000000000) (60802118801 / 500000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (60309378527 / 500000000000) (60802118801 / 500000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(947417 / 1000000)
  have hx98 : Bounds (1947417 / 1000000) (1947417 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((947417 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(947417 / 1000000)
  have hx99 : Bounds (1947417 / 1000000) (1947417 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((947417 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (666503879 / 1000000000) (16662597 / 25000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (129796098453 / 100000000000) (648980493239 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(947417 / 1000000)
  have hx102 : Bounds (-947417 / 1000000) (-947417 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((947417 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (52583 / 1000000) (52583 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(947417 / 1000000)
  have hx104 : Bounds (52583 / 1000000) (52583 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(947417 / 1000000)
  have hx105 : Bounds (-947417 / 1000000) (-947417 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((947417 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (52583 / 1000000) (52583 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(947417 / 1000000)
  have hx107 : Bounds (52583 / 1000000) (52583 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-368170301 / 125000000) (-2945362403 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-309751983 / 2000000000) (-38718997809 / 250000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (114308499303 / 100000000000) (571542497621 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (114308499303 / 200000000000) (571542497621 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (114308499303 / 200000000000) (571542497621 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-571542497621 / 1000000000000) (-114308499303 / 200000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (121604682379 / 1000000000000) (24320936897 / 200000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (121604682379 / 1000000000000) (24320936897 / 200000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (947417 / 1000000)
  have hx117 : Bounds (121604682379 / 1000000000000) (24320936897 / 200000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(947963 / 1000000)
  have hx119 : Bounds (1947963 / 1000000) (1947963 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((947963 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(947963 / 1000000)
  have hx120 : Bounds (1947963 / 1000000) (1947963 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((947963 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (666784211 / 1000000000) (166696053 / 250000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (324717743003 / 250000000000) (1298870973961 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(947963 / 1000000)
  have hx123 : Bounds (-947963 / 1000000) (-947963 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((947963 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (52037 / 1000000) (52037 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(947963 / 1000000)
  have hx125 : Bounds (52037 / 1000000) (52037 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(947963 / 1000000)
  have hx126 : Bounds (-947963 / 1000000) (-947963 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((947963 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (52037 / 1000000) (52037 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(947963 / 1000000)
  have hx128 : Bounds (52037 / 1000000) (52037 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-2955800277 / 1000000000) (-184737517 / 62500000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-30762195803 / 200000000000) (-76905489377 / 500000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1145059992997 / 1000000000000) (1145059995207 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (286264998249 / 500000000000) (143132499401 / 250000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (286264998249 / 500000000000) (143132499401 / 250000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-143132499401 / 250000000000) (-286264998249 / 500000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (30154295599 / 250000000000) (60308592251 / 500000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (30154295599 / 250000000000) (60308592251 / 500000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (947963 / 1000000)
  have hx138 : Bounds (30154295599 / 250000000000) (60308592251 / 500000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (947417 / 1000000) (947963 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (947963 / 1000000) ≤ (60308592251 / 500000000000) := hx138.2
      have h2 : (60309378527 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (60802118801 / 500000000000) := hx96.2
      have h2 : (121604682379 / 1000000000000) ≤ biasE (947417 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (213966317021 / 200000000000) (1070681723129 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (32260439013 / 250000000000) (4068732333 / 31250000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (32260439013 / 250000000000) (4068732333 / 31250000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(946511 / 1000000)
  have hx143 : Bounds (1946511 / 1000000) (1946511 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((946511 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(946511 / 1000000)
  have hx144 : Bounds (1946511 / 1000000) (1946511 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((946511 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (666038539 / 1000000000) (33301927 / 50000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1296451342587 / 1000000000000) (648225672267 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(946511 / 1000000)
  have hx147 : Bounds (-946511 / 1000000) (-946511 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((946511 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (53489 / 1000000) (53489 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(946511 / 1000000)
  have hx149 : Bounds (53489 / 1000000) (53489 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(946511 / 1000000)
  have hx150 : Bounds (-946511 / 1000000) (-946511 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((946511 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (53489 / 1000000) (53489 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(946511 / 1000000)
  have hx152 : Bounds (53489 / 1000000) (53489 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-366034907 / 125000000) (-2928279251 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-1253045833 / 8000000000) (-19578841107 / 125000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (569910306731 / 500000000000) (569910307839 / 500000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (569910306731 / 1000000000000) (569910307839 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (569910306731 / 1000000000000) (569910307839 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-569910307839 / 1000000000000) (-569910306731 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (123236872161 / 1000000000000) (123236874269 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (123236872161 / 1000000000000) (123236874269 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (946511 / 1000000)
  have hx162 : Bounds (123236872161 / 1000000000000) (123236874269 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(23677 / 25000)
  have hx164 : Bounds (48677 / 25000) (48677 / 25000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23677 / 25000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(23677 / 25000)
  have hx165 : Bounds (48677 / 25000) (48677 / 25000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23677 / 25000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (333165407 / 500000000) (133266163 / 200000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1297399401323 / 1000000000000) (1297399403271 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(23677 / 25000)
  have hx168 : Bounds (-23677 / 25000) (-23677 / 25000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23677 / 25000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (1323 / 25000) (1323 / 25000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(23677 / 25000)
  have hx170 : Bounds (1323 / 25000) (1323 / 25000) x170 := by
    exact hx169
  let x171 : ℝ := -(23677 / 25000)
  have hx171 : Bounds (-23677 / 25000) (-23677 / 25000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23677 / 25000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (1323 / 25000) (1323 / 25000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(23677 / 25000)
  have hx173 : Bounds (1323 / 25000) (1323 / 25000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-1469486971 / 500000000) (-2938973937 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-155530501011 / 1000000000000) (-77765250373 / 500000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (142733612539 / 125000000000) (45674756101 / 40000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (142733612539 / 250000000000) (570934451263 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (142733612539 / 250000000000) (570934451263 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-570934451263 / 1000000000000) (-142733612539 / 250000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (122212728737 / 1000000000000) (30553182711 / 250000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (122212728737 / 1000000000000) (30553182711 / 250000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (23677 / 25000)
  have hx183 : Bounds (122212728737 / 1000000000000) (30553182711 / 250000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(946511 / 1000000)
  have hx184 : Bounds (61069720781 / 500000000000) (15404399637 / 125000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((946511 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(23677 / 25000)
  have hx185 : Bounds (122212866321 / 1000000000000) (4932371223 / 40000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((23677 / 25000) : ℝ)) <;> norm_num
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
  have hc : Bounds (946511 / 1000000) (23677 / 25000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (946511 / 1000000) ≤ (15404399637 / 125000000000) := hx184.2
      have h2 : (123236872161 / 1000000000000) ≤ biasE (946511 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (23677 / 25000) ≤ (30553182711 / 250000000000) := hx183.2
      have h2 : (122212866321 / 1000000000000) ≤ x141 * (23677 / 25000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1947417 / 1000000) (1947963 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-947963 / 1000000) (-947417 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (52037 / 1000000) (52583 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (52037 / 1000000) (52583 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (3803510640321 / 200000000000) (9608547764091 / 500000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (3703510640321 / 100000000000) (9358547764091 / 250000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (3703510640321 / 100000000000) (9358547764091 / 250000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (3611866281 / 1000000000) (3622584489 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (3611866281 / 2000000000) (3622584489 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (3611866281 / 2000000000) (3622584489 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1946511 / 1000000) (48677 / 25000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-23677 / 25000) (-946511 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (1323 / 25000) (53489 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (1323 / 25000) (53489 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (18695432705789 / 1000000000000) (18896447467877 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (18195432705789 / 500000000000) (18396447467877 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (18195432705789 / 500000000000) (18396447467877 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (359431779 / 100000000) (3605304757 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (359431779 / 200000000) (3605304757 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (359431779 / 200000000) (3605304757 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (17973931987 / 62500000000) (18130871619 / 62500000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (60309378527 / 250000000000) (60802118801 / 250000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-60802118801 / 250000000000) (-60309378527 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (11093609147 / 250000000000) (12214107949 / 250000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (11093609147 / 250000000000) (12214107949 / 250000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1710971758173 / 1000000000000) (1717038029973 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1717038029973 / 1000000000000) (-1710971758173 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-334532718677 / 200000000000) (-1662115326377 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-334532718677 / 200000000000) (-1662115326377 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (839259163661 / 500000000000) (842493530569 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (5854733937 / 1000000000000) (22871734761 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1671 / 51200) (169 / 5120) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1671 / 51200) ≤ m → m ≤ (169 / 5120) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (169 / 5120) (1709 / 51200) m) :
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
  have hx0 : Bounds (169 / 2560) (1709 / 25600) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1709 / 25600) (-169 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (23891 / 25600) (2391 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (23891 / 25600) (2391 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (169 / 1280) (1709 / 12800) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1709 / 12800) (-169 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (11091 / 12800) (1111 / 1280) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (11091 / 12800) (1111 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2391 / 2560)
  have hx9 : Bounds (4951 / 2560) (4951 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2391 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2391 / 2560)
  have hx10 : Bounds (4951 / 2560) (4951 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2391 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (659582317 / 1000000000) (329791159 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (19931592111 / 15625000000) (1275621897039 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2391 / 2560)
  have hx13 : Bounds (-2391 / 2560) (-2391 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2391 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (169 / 2560) (169 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2391 / 2560)
  have hx15 : Bounds (169 / 2560) (169 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(2391 / 2560)
  have hx16 : Bounds (-2391 / 2560) (-2391 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2391 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (169 / 2560) (169 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2391 / 2560)
  have hx18 : Bounds (169 / 2560) (169 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-169866489 / 62500000) (-135893191 / 50000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-179421479007 / 1000000000000) (-89710739371 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1096200416097 / 1000000000000) (1096200418297 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (34256263003 / 62500000000) (548100209149 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (34256263003 / 62500000000) (548100209149 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-548100209149 / 1000000000000) (-34256263003 / 62500000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (145046970851 / 1000000000000) (18130871619 / 125000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (145046970851 / 1000000000000) (18130871619 / 125000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2391 / 2560)
  have hx28 : Bounds (145046970851 / 1000000000000) (18130871619 / 125000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(23891 / 25600)
  have hx30 : Bounds (49491 / 25600) (49491 / 25600) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23891 / 25600) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(23891 / 25600)
  have hx31 : Bounds (49491 / 25600) (49491 / 25600) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23891 / 25600) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (659198483 / 1000000000) (164799621 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (1274390317271 / 1000000000000) (254878063841 / 200000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(23891 / 25600)
  have hx34 : Bounds (-23891 / 25600) (-23891 / 25600) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23891 / 25600) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1709 / 25600) (1709 / 25600) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(23891 / 25600)
  have hx36 : Bounds (1709 / 25600) (1709 / 25600) x36 := by
    exact hx35
  let x37 : ℝ := -(23891 / 25600)
  have hx37 : Bounds (-23891 / 25600) (-23891 / 25600) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23891 / 25600) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1709 / 25600) (1709 / 25600) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(23891 / 25600)
  have hx39 : Bounds (1709 / 25600) (1709 / 25600) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-2706683949 / 1000000000) (-541336789 / 200000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-36138459913 / 200000000000) (-180692299297 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (546849008853 / 500000000000) (273424504977 / 250000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (546849008853 / 1000000000000) (273424504977 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (546849008853 / 1000000000000) (273424504977 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-273424504977 / 500000000000) (-546849008853 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (73149085023 / 500000000000) (146298172147 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (73149085023 / 500000000000) (146298172147 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (23891 / 25600)
  have hx49 : Bounds (73149085023 / 500000000000) (146298172147 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (145046970851 / 1000000000000) (146298172147 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1111 / 1280)
  have hx52 : Bounds (2391 / 1280) (2391 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1111 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1111 / 1280)
  have hx53 : Bounds (2391 / 1280) (2391 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1111 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (62485161 / 100000000) (624851611 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1167203280867 / 1000000000000) (72950205171 / 62500000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1111 / 1280)
  have hx56 : Bounds (-1111 / 1280) (-1111 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1111 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (169 / 1280) (169 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1111 / 1280)
  have hx58 : Bounds (169 / 1280) (169 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(1111 / 1280)
  have hx59 : Bounds (-1111 / 1280) (-1111 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1111 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (169 / 1280) (169 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1111 / 1280)
  have hx61 : Bounds (169 / 1280) (169 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2024716643 / 1000000000) (-12654479 / 6250000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-33415733659 / 125000000000) (-2138606951 / 8000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (179975482319 / 200000000000) (899877413861 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (449938705797 / 1000000000000) (449938706931 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (449938705797 / 1000000000000) (449938706931 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-449938706931 / 1000000000000) (-449938705797 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (243208473069 / 1000000000000) (243208475203 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (243208473069 / 1000000000000) (243208475203 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1111 / 1280)
  have hx71 : Bounds (243208473069 / 1000000000000) (243208475203 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(11091 / 12800)
  have hx73 : Bounds (23891 / 12800) (23891 / 12800) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11091 / 12800) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(11091 / 12800)
  have hx74 : Bounds (23891 / 12800) (23891 / 12800) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11091 / 12800) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (78007081 / 125000000) (624056649 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (582395991303 / 500000000000) (582395992237 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(11091 / 12800)
  have hx77 : Bounds (-11091 / 12800) (-11091 / 12800) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11091 / 12800) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1709 / 12800) (1709 / 12800) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(11091 / 12800)
  have hx79 : Bounds (1709 / 12800) (1709 / 12800) x79 := by
    exact hx78
  let x80 : ℝ := -(11091 / 12800)
  have hx80 : Bounds (-11091 / 12800) (-11091 / 12800) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11091 / 12800) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1709 / 12800) (1709 / 12800) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(11091 / 12800)
  have hx82 : Bounds (1709 / 12800) (1709 / 12800) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-3932689 / 1953125) (-402707353 / 200000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-6720965501 / 25000000000) (-268838619639 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (447976681283 / 500000000000) (179190672967 / 200000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (447976681283 / 1000000000000) (223988341209 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (447976681283 / 1000000000000) (223988341209 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-223988341209 / 500000000000) (-447976681283 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (122585248791 / 500000000000) (245170499717 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (122585248791 / 500000000000) (245170499717 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (11091 / 12800)
  have hx92 : Bounds (122585248791 / 500000000000) (245170499717 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (243208473069 / 1000000000000) (245170499717 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (60802118267 / 500000000000) (122585249859 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (60802118267 / 500000000000) (122585249859 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(946873 / 1000000)
  have hx98 : Bounds (1946873 / 1000000) (1946873 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((946873 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(946873 / 1000000)
  have hx99 : Bounds (1946873 / 1000000) (1946873 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((946873 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (133244899 / 200000000) (41639031 / 62500000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (648527240627 / 500000000000) (648527241601 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(946873 / 1000000)
  have hx102 : Bounds (-946873 / 1000000) (-946873 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((946873 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (53127 / 1000000) (53127 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(946873 / 1000000)
  have hx104 : Bounds (53127 / 1000000) (53127 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(946873 / 1000000)
  have hx105 : Bounds (-946873 / 1000000) (-946873 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((946873 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (53127 / 1000000) (53127 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(946873 / 1000000)
  have hx107 : Bounds (53127 / 1000000) (53127 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-366883751 / 125000000) (-2935070003 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-38982866079 / 250000000000) (-155931464049 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (570561508469 / 500000000000) (1141123019153 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (570561508469 / 1000000000000) (570561509577 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (570561508469 / 1000000000000) (570561509577 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-570561509577 / 1000000000000) (-570561508469 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (122585670423 / 1000000000000) (122585672531 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (122585670423 / 1000000000000) (122585672531 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (946873 / 1000000)
  have hx117 : Bounds (122585670423 / 1000000000000) (122585672531 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(473709 / 500000)
  have hx119 : Bounds (973709 / 500000) (973709 / 500000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((473709 / 500000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(473709 / 500000)
  have hx120 : Bounds (973709 / 500000) (973709 / 500000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((473709 / 500000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (83313049 / 125000000) (666504393 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1297962650059 / 1000000000000) (162245331501 / 125000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(473709 / 500000)
  have hx123 : Bounds (-473709 / 500000) (-473709 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((473709 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (26291 / 500000) (26291 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(473709 / 500000)
  have hx125 : Bounds (26291 / 500000) (26291 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := -(473709 / 500000)
  have hx126 : Bounds (-473709 / 500000) (-473709 / 500000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((473709 / 500000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (26291 / 500000) (26291 / 500000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(473709 / 500000)
  have hx128 : Bounds (26291 / 500000) (26291 / 500000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-117815257 / 40000000) (-147269071 / 50000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-15487404609 / 100000000000) (-77437022913 / 500000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1143088603969 / 1000000000000) (571544303091 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (17860759437 / 31250000000) (571544303091 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (17860759437 / 31250000000) (571544303091 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-571544303091 / 1000000000000) (-17860759437 / 31250000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (121602876909 / 1000000000000) (15200359877 / 125000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (121602876909 / 1000000000000) (15200359877 / 125000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (473709 / 500000)
  have hx138 : Bounds (121602876909 / 1000000000000) (15200359877 / 125000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (946873 / 1000000) (473709 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (473709 / 500000) ≤ (15200359877 / 125000000000) := hx138.2
      have h2 : (60802118267 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (122585249859 / 1000000000000) := hx96.2
      have h2 : (122585670423 / 1000000000000) ≤ biasE (946873 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (133835215391 / 125000000000) (33485412917 / 31250000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (130199433511 / 1000000000000) (13135416669 / 100000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (130199433511 / 1000000000000) (13135416669 / 100000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(118243 / 125000)
  have hx143 : Bounds (243243 / 125000) (243243 / 125000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((118243 / 125000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(118243 / 125000)
  have hx144 : Bounds (243243 / 125000) (243243 / 125000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((118243 / 125000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (332873603 / 500000000) (665747207 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (161938347629 / 125000000000) (1295506782979 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(118243 / 125000)
  have hx147 : Bounds (-118243 / 125000) (-118243 / 125000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((118243 / 125000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (6757 / 125000) (6757 / 125000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(118243 / 125000)
  have hx149 : Bounds (6757 / 125000) (6757 / 125000) x149 := by
    exact hx148
  let x150 : ℝ := -(118243 / 125000)
  have hx150 : Bounds (-118243 / 125000) (-118243 / 125000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((118243 / 125000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (6757 / 125000) (6757 / 125000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(118243 / 125000)
  have hx152 : Bounds (6757 / 125000) (6757 / 125000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-583546947 / 200000000) (-291773473 / 100000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-39430267209 / 250000000000) (-39430267141 / 250000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (284446428049 / 250000000000) (227557142883 / 200000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (284446428049 / 500000000000) (71111607151 / 125000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (284446428049 / 500000000000) (71111607151 / 125000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-71111607151 / 125000000000) (-284446428049 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (15531790349 / 125000000000) (62127162451 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (15531790349 / 125000000000) (62127162451 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (118243 / 125000)
  have hx162 : Bounds (15531790349 / 125000000000) (62127162451 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(59157 / 62500)
  have hx164 : Bounds (121657 / 62500) (121657 / 62500) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((59157 / 62500) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(59157 / 62500)
  have hx165 : Bounds (121657 / 62500) (121657 / 62500) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((59157 / 62500) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (166509763 / 250000000) (666039053 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (648226503593 / 500000000000) (648226504567 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(59157 / 62500)
  have hx168 : Bounds (-59157 / 62500) (-59157 / 62500) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((59157 / 62500) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (3343 / 62500) (3343 / 62500) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(59157 / 62500)
  have hx170 : Bounds (3343 / 62500) (3343 / 62500) x170 := by
    exact hx169
  let x171 : ℝ := -(59157 / 62500)
  have hx171 : Bounds (-59157 / 62500) (-59157 / 62500) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((59157 / 62500) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (3343 / 62500) (3343 / 62500) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(59157 / 62500)
  have hx173 : Bounds (3343 / 62500) (3343 / 62500) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-91509311 / 31250000) (-2928297947 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-156628800857 / 1000000000000) (-156628800589 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1139824206329 / 1000000000000) (227964841709 / 200000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (142478025791 / 250000000000) (569912104273 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (142478025791 / 250000000000) (569912104273 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-569912104273 / 1000000000000) (-142478025791 / 250000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (123235075727 / 1000000000000) (30808769459 / 250000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (123235075727 / 1000000000000) (30808769459 / 250000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (59157 / 62500)
  have hx183 : Bounds (123235075727 / 1000000000000) (30808769459 / 250000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(118243 / 125000)
  have hx184 : Bounds (123161372933 / 1000000000000) (3882927683 / 31250000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((118243 / 125000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(59157 / 62500)
  have hx185 : Bounds (123235326211 / 1000000000000) (124328295023 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((59157 / 62500) : ℝ)) <;> norm_num
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
  have hc : Bounds (118243 / 125000) (59157 / 62500) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (118243 / 125000) ≤ (3882927683 / 31250000000) := hx184.2
      have h2 : (15531790349 / 125000000000) ≤ biasE (118243 / 125000) := hx162.1
      linarith
    · have h1 : biasE (59157 / 62500) ≤ (30808769459 / 250000000000) := hx183.2
      have h2 : (123235326211 / 1000000000000) ≤ x141 * (59157 / 62500) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1946873 / 1000000) (973709 / 500000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-473709 / 500000) (-946873 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (26291 / 500000) (53127 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (26291 / 500000) (53127 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (18822820787923 / 1000000000000) (9508957437907 / 500000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (18322820787923 / 500000000000) (9258957437907 / 250000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (18322820787923 / 500000000000) (9258957437907 / 250000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1800647249 / 500000000) (1805942909 / 500000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1800647249 / 1000000000) (1805942909 / 1000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1800647249 / 1000000000) (1805942909 / 1000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (243243 / 125000) (121657 / 62500) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-59157 / 62500) (-118243 / 125000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (3343 / 62500) (6757 / 125000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (3343 / 62500) (6757 / 125000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (739973360959 / 40000000000) (18695782231529 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (719973360959 / 20000000000) (18195782231529 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (719973360959 / 20000000000) (18195782231529 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (223967621 / 62500000) (718867401 / 200000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (223967621 / 125000000) (718867401 / 400000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (223967621 / 125000000) (718867401 / 400000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (145046970851 / 500000000000) (146298172147 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (60802118267 / 250000000000) (122585249859 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-122585249859 / 500000000000) (-60802118267 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (701928781 / 15625000000) (24693935613 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (701928781 / 15625000000) (24693935613 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (852492131301 / 500000000000) (1710982818959 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1710982818959 / 1000000000000) (-852492131301 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-66642375079 / 40000000000) (-103474774461 / 62500000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-66642375079 / 40000000000) (-103474774461 / 62500000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1672128260409 / 1000000000000) (839263650289 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (3034441717 / 500000000000) (11465454601 / 500000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (169 / 5120) (1709 / 51200) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (169 / 5120) ≤ m → m ≤ (1709 / 51200) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1709 / 51200) (27 / 800) m) :
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
  have hx0 : Bounds (1709 / 25600) (27 / 400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-27 / 400) (-1709 / 25600) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (373 / 400) (23891 / 25600) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (373 / 400) (23891 / 25600) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1709 / 12800) (27 / 200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-27 / 200) (-1709 / 12800) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (173 / 200) (11091 / 12800) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (173 / 200) (11091 / 12800) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(23891 / 25600)
  have hx9 : Bounds (49491 / 25600) (49491 / 25600) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23891 / 25600) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(23891 / 25600)
  have hx10 : Bounds (49491 / 25600) (49491 / 25600) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23891 / 25600) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (659198483 / 1000000000) (164799621 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (1274390317271 / 1000000000000) (254878063841 / 200000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(23891 / 25600)
  have hx13 : Bounds (-23891 / 25600) (-23891 / 25600) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23891 / 25600) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1709 / 25600) (1709 / 25600) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(23891 / 25600)
  have hx15 : Bounds (1709 / 25600) (1709 / 25600) x15 := by
    exact hx14
  let x16 : ℝ := -(23891 / 25600)
  have hx16 : Bounds (-23891 / 25600) (-23891 / 25600) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23891 / 25600) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1709 / 25600) (1709 / 25600) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(23891 / 25600)
  have hx18 : Bounds (1709 / 25600) (1709 / 25600) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-2706683949 / 1000000000) (-541336789 / 200000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-36138459913 / 200000000000) (-180692299297 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (546849008853 / 500000000000) (273424504977 / 250000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (546849008853 / 1000000000000) (273424504977 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (546849008853 / 1000000000000) (273424504977 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-273424504977 / 500000000000) (-546849008853 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (73149085023 / 500000000000) (146298172147 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (73149085023 / 500000000000) (146298172147 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (23891 / 25600)
  have hx28 : Bounds (73149085023 / 500000000000) (146298172147 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(373 / 400)
  have hx30 : Bounds (773 / 400) (773 / 400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((373 / 400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(373 / 400)
  have hx31 : Bounds (773 / 400) (773 / 400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((373 / 400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (658814501 / 1000000000) (329407251 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (636579511591 / 500000000000) (254631805023 / 200000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(373 / 400)
  have hx34 : Bounds (-373 / 400) (-373 / 400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((373 / 400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (27 / 400) (27 / 400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(373 / 400)
  have hx36 : Bounds (27 / 400) (27 / 400) x36 := by
    exact hx35
  let x37 : ℝ := -(373 / 400)
  have hx37 : Bounds (-373 / 400) (-373 / 400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((373 / 400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (27 / 400) (27 / 400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(373 / 400)
  have hx39 : Bounds (27 / 400) (27 / 400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-2695627683 / 1000000000) (-2695627679 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-181954868603 / 1000000000000) (-45488717083 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1091204154579 / 1000000000000) (1091204156783 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (545602077289 / 1000000000000) (68200259799 / 125000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (545602077289 / 1000000000000) (68200259799 / 125000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-68200259799 / 125000000000) (-545602077289 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (18443137701 / 125000000000) (147545103711 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (18443137701 / 125000000000) (147545103711 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (373 / 400)
  have hx49 : Bounds (18443137701 / 125000000000) (147545103711 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (73149085023 / 500000000000) (147545103711 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(11091 / 12800)
  have hx52 : Bounds (23891 / 12800) (23891 / 12800) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11091 / 12800) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(11091 / 12800)
  have hx53 : Bounds (23891 / 12800) (23891 / 12800) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11091 / 12800) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (78007081 / 125000000) (624056649 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (582395991303 / 500000000000) (582395992237 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(11091 / 12800)
  have hx56 : Bounds (-11091 / 12800) (-11091 / 12800) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11091 / 12800) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1709 / 12800) (1709 / 12800) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(11091 / 12800)
  have hx58 : Bounds (1709 / 12800) (1709 / 12800) x58 := by
    exact hx57
  let x59 : ℝ := -(11091 / 12800)
  have hx59 : Bounds (-11091 / 12800) (-11091 / 12800) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11091 / 12800) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1709 / 12800) (1709 / 12800) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(11091 / 12800)
  have hx61 : Bounds (1709 / 12800) (1709 / 12800) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-3932689 / 1953125) (-402707353 / 200000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-6720965501 / 25000000000) (-268838619639 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (447976681283 / 500000000000) (179190672967 / 200000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (447976681283 / 1000000000000) (223988341209 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (447976681283 / 1000000000000) (223988341209 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-223988341209 / 500000000000) (-447976681283 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (122585248791 / 500000000000) (245170499717 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (122585248791 / 500000000000) (245170499717 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (11091 / 12800)
  have hx71 : Bounds (122585248791 / 500000000000) (245170499717 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(173 / 200)
  have hx73 : Bounds (373 / 200) (373 / 200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((173 / 200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(173 / 200)
  have hx74 : Bounds (373 / 200) (373 / 200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((173 / 200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (623261053 / 1000000000) (311630527 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (232476372769 / 200000000000) (116238186571 / 100000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(173 / 200)
  have hx77 : Bounds (-173 / 200) (-173 / 200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((173 / 200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (27 / 200) (27 / 200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(173 / 200)
  have hx79 : Bounds (27 / 200) (27 / 200) x79 := by
    exact hx78
  let x80 : ℝ := -(173 / 200)
  have hx80 : Bounds (-173 / 200) (-173 / 200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((173 / 200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (27 / 200) (27 / 200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(173 / 200)
  have hx82 : Bounds (27 / 200) (27 / 200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1001240251 / 500000000) (-2002480499 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-27033486777 / 100000000000) (-54066973473 / 200000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (35681879843 / 40000000000) (178409399669 / 200000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (446023498037 / 1000000000000) (446023499173 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (446023498037 / 1000000000000) (446023499173 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-446023499173 / 1000000000000) (-446023498037 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (247123680827 / 1000000000000) (247123682963 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (247123680827 / 1000000000000) (247123682963 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (173 / 200)
  have hx92 : Bounds (247123680827 / 1000000000000) (247123682963 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (122585248791 / 500000000000) (247123682963 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (122585248791 / 1000000000000) (61780920741 / 500000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (122585248791 / 1000000000000) (61780920741 / 500000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(94633 / 100000)
  have hx98 : Bounds (194633 / 100000) (194633 / 100000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((94633 / 100000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(94633 / 100000)
  have hx99 : Bounds (194633 / 100000) (194633 / 100000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((94633 / 100000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (166486387 / 250000000) (665945549 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (648074899219 / 500000000000) (648074900193 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(94633 / 100000)
  have hx102 : Bounds (-94633 / 100000) (-94633 / 100000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((94633 / 100000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (5367 / 100000) (5367 / 100000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(94633 / 100000)
  have hx104 : Bounds (5367 / 100000) (5367 / 100000) x104 := by
    exact hx103
  let x105 : ℝ := -(94633 / 100000)
  have hx105 : Bounds (-94633 / 100000) (-94633 / 100000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((94633 / 100000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (5367 / 100000) (5367 / 100000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(94633 / 100000)
  have hx107 : Bounds (5367 / 100000) (5367 / 100000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-584980219 / 200000000) (-292490109 / 100000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-156979441769 / 1000000000000) (-313958883 / 2000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1139170356669 / 1000000000000) (569585179443 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (284792589167 / 500000000000) (569585179443 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (284792589167 / 500000000000) (569585179443 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-569585179443 / 1000000000000) (-284792589167 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (123562000557 / 1000000000000) (61781001333 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (123562000557 / 1000000000000) (61781001333 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (94633 / 100000)
  have hx117 : Bounds (123562000557 / 1000000000000) (61781001333 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(473437 / 500000)
  have hx119 : Bounds (973437 / 500000) (973437 / 500000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((473437 / 500000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(473437 / 500000)
  have hx120 : Bounds (973437 / 500000) (973437 / 500000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((473437 / 500000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (666225009 / 1000000000) (66622501 / 100000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1297056148171 / 1000000000000) (1297056150119 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(473437 / 500000)
  have hx123 : Bounds (-473437 / 500000) (-473437 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((473437 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (26563 / 500000) (26563 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(473437 / 500000)
  have hx125 : Bounds (26563 / 500000) (26563 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := -(473437 / 500000)
  have hx126 : Bounds (-473437 / 500000) (-473437 / 500000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((473437 / 500000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (26563 / 500000) (26563 / 500000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(473437 / 500000)
  have hx128 : Bounds (26563 / 500000) (26563 / 500000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-2935088831 / 1000000000) (-1467544413 / 500000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-38982382309 / 250000000000) (-15592952897 / 100000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (228225323787 / 200000000000) (1141126621149 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (570563309467 / 1000000000000) (22822532423 / 40000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (570563309467 / 1000000000000) (22822532423 / 40000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-22822532423 / 40000000000) (-570563309467 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (4903354777 / 40000000000) (122583871533 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (4903354777 / 40000000000) (122583871533 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (473437 / 500000)
  have hx138 : Bounds (4903354777 / 40000000000) (122583871533 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (94633 / 100000) (473437 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (473437 / 500000) ≤ (122583871533 / 1000000000000) := hx138.2
      have h2 : (122585248791 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (61780920741 / 500000000000) := hx96.2
      have h2 : (123562000557 / 1000000000000) ≤ biasE (94633 / 100000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1071533213343 / 1000000000000) (536193029491 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (26270833109 / 200000000000) (33126499057 / 250000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (26270833109 / 200000000000) (33126499057 / 250000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(945377 / 1000000)
  have hx143 : Bounds (1945377 / 1000000) (1945377 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((945377 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(945377 / 1000000)
  have hx144 : Bounds (1945377 / 1000000) (1945377 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((945377 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (166363947 / 250000000) (665455789 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (323640596123 / 250000000000) (647281193219 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(945377 / 1000000)
  have hx147 : Bounds (-945377 / 1000000) (-945377 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((945377 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (54623 / 1000000) (54623 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(945377 / 1000000)
  have hx149 : Bounds (54623 / 1000000) (54623 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(945377 / 1000000)
  have hx150 : Bounds (-945377 / 1000000) (-945377 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((945377 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (54623 / 1000000) (54623 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(945377 / 1000000)
  have hx152 : Bounds (54623 / 1000000) (54623 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-1453650121 / 500000000) (-2907300237 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-158805461119 / 1000000000000) (-31761092169 / 200000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1135756923373 / 1000000000000) (1135756925593 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (283939230843 / 500000000000) (567878462797 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (283939230843 / 500000000000) (567878462797 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-567878462797 / 1000000000000) (-283939230843 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (125268717203 / 1000000000000) (62634359657 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (125268717203 / 1000000000000) (62634359657 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (945377 / 1000000)
  have hx162 : Bounds (125268717203 / 1000000000000) (62634359657 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(189189 / 200000)
  have hx164 : Bounds (389189 / 200000) (389189 / 200000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((189189 / 200000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(189189 / 200000)
  have hx165 : Bounds (389189 / 200000) (389189 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((189189 / 200000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (16643693 / 25000000) (665747721 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (259101689399 / 200000000000) (647754224471 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(189189 / 200000)
  have hx168 : Bounds (-189189 / 200000) (-189189 / 200000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((189189 / 200000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (10811 / 200000) (10811 / 200000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(189189 / 200000)
  have hx170 : Bounds (10811 / 200000) (10811 / 200000) x170 := by
    exact hx169
  let x171 : ℝ := -(189189 / 200000)
  have hx171 : Bounds (-189189 / 200000) (-189189 / 200000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((189189 / 200000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (10811 / 200000) (10811 / 200000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(189189 / 200000)
  have hx173 : Bounds (10811 / 200000) (10811 / 200000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-1458876617 / 500000000) (-2917753229 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-19714893883 / 125000000000) (-157719150793 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1137789295931 / 1000000000000) (1137789298149 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (113778929593 / 200000000000) (22755785963 / 40000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (113778929593 / 200000000000) (22755785963 / 40000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-22755785963 / 40000000000) (-113778929593 / 200000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (4970101237 / 40000000000) (24850506607 / 200000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (4970101237 / 40000000000) (24850506607 / 200000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (189189 / 200000)
  have hx183 : Bounds (4970101237 / 40000000000) (24850506607 / 200000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(945377 / 1000000)
  have hx184 : Bounds (1552240087 / 12500000000) (125268121197 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((945377 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(189189 / 200000)
  have hx185 : Bounds (62126908063 / 500000000000) (62671692301 / 500000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((189189 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (945377 / 1000000) (189189 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (945377 / 1000000) ≤ (125268121197 / 1000000000000) := hx184.2
      have h2 : (125268717203 / 1000000000000) ≤ biasE (945377 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (189189 / 200000) ≤ (24850506607 / 200000000000) := hx183.2
      have h2 : (62126908063 / 500000000000) ≤ x141 * (189189 / 200000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (194633 / 100000) (973437 / 500000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-473437 / 500000) (-94633 / 100000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (26563 / 500000) (5367 / 100000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (26563 / 500000) (5367 / 100000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (4658095770449 / 250000000000) (752927003727 / 40000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (4533095770449 / 125000000000) (732927003727 / 20000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (4533095770449 / 125000000000) (732927003727 / 20000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1795423319 / 500000000) (45016423 / 12500000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1795423319 / 1000000000) (45016423 / 25000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1795423319 / 1000000000) (45016423 / 25000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1945377 / 1000000) (389189 / 200000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-189189 / 200000) (-945377 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (10811 / 200000) (54623 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (10811 / 200000) (54623 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (9153653223001 / 500000000000) (9249838127833 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (8903653223001 / 250000000000) (8999838127833 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (8903653223001 / 250000000000) (8999838127833 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (142910241 / 40000000) (716700191 / 200000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (142910241 / 80000000) (716700191 / 400000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (142910241 / 80000000) (716700191 / 400000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (73149085023 / 250000000000) (147545103711 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (122585248791 / 500000000000) (61780920741 / 250000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-61780920741 / 250000000000) (-122585248791 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (5684082141 / 125000000000) (623996373 / 12500000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (5684082141 / 125000000000) (623996373 / 12500000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1699062949469 / 1000000000000) (1704995220469 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1704995220469 / 1000000000000) (-1699062949469 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-1659522563341 / 1000000000000) (-1649143239629 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-1659522563341 / 1000000000000) (-1649143239629 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (104112343541 / 62500000000) (1672137135077 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1254986663 / 200000000000) (2874236931 / 125000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1709 / 51200) (27 / 800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1709 / 51200) ≤ m → m ≤ (27 / 800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (27 / 800) (1747 / 51200) m) :
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
  have hx0 : Bounds (27 / 400) (1747 / 25600) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1747 / 25600) (-27 / 400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (23853 / 25600) (373 / 400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (23853 / 25600) (373 / 400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (27 / 200) (1747 / 12800) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1747 / 12800) (-27 / 200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (11053 / 12800) (173 / 200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (11053 / 12800) (173 / 200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(373 / 400)
  have hx9 : Bounds (773 / 400) (773 / 400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((373 / 400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(373 / 400)
  have hx10 : Bounds (773 / 400) (773 / 400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((373 / 400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (658814501 / 1000000000) (329407251 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (636579511591 / 500000000000) (254631805023 / 200000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(373 / 400)
  have hx13 : Bounds (-373 / 400) (-373 / 400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((373 / 400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (27 / 400) (27 / 400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(373 / 400)
  have hx15 : Bounds (27 / 400) (27 / 400) x15 := by
    exact hx14
  let x16 : ℝ := -(373 / 400)
  have hx16 : Bounds (-373 / 400) (-373 / 400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((373 / 400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (27 / 400) (27 / 400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(373 / 400)
  have hx18 : Bounds (27 / 400) (27 / 400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-2695627683 / 1000000000) (-2695627679 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-181954868603 / 1000000000000) (-45488717083 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1091204154579 / 1000000000000) (1091204156783 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (545602077289 / 1000000000000) (68200259799 / 125000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (545602077289 / 1000000000000) (68200259799 / 125000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-68200259799 / 125000000000) (-545602077289 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (18443137701 / 125000000000) (147545103711 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (18443137701 / 125000000000) (147545103711 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (373 / 400)
  have hx28 : Bounds (18443137701 / 125000000000) (147545103711 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(23853 / 25600)
  have hx30 : Bounds (49453 / 25600) (49453 / 25600) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23853 / 25600) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(23853 / 25600)
  have hx31 : Bounds (49453 / 25600) (49453 / 25600) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23853 / 25600) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (164607593 / 250000000) (658430373 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (635964007549 / 500000000000) (1271928017031 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(23853 / 25600)
  have hx34 : Bounds (-23853 / 25600) (-23853 / 25600) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23853 / 25600) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1747 / 25600) (1747 / 25600) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(23853 / 25600)
  have hx36 : Bounds (1747 / 25600) (1747 / 25600) x36 := by
    exact hx35
  let x37 : ℝ := -(23853 / 25600)
  have hx37 : Bounds (-23853 / 25600) (-23853 / 25600) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23853 / 25600) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1747 / 25600) (1747 / 25600) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(23853 / 25600)
  have hx39 : Bounds (1747 / 25600) (1747 / 25600) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1342346161 / 500000000) (-1342346159 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-91604638409 / 500000000000) (-1431322473 / 7812500000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (27217968457 / 25000000000) (1088718740487 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (27217968457 / 50000000000) (136089842561 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (27217968457 / 50000000000) (136089842561 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-136089842561 / 250000000000) (-27217968457 / 50000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (37196952439 / 250000000000) (7439390593 / 50000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (37196952439 / 250000000000) (7439390593 / 50000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (23853 / 25600)
  have hx49 : Bounds (37196952439 / 250000000000) (7439390593 / 50000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (18443137701 / 125000000000) (7439390593 / 50000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(173 / 200)
  have hx52 : Bounds (373 / 200) (373 / 200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((173 / 200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(173 / 200)
  have hx53 : Bounds (373 / 200) (373 / 200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((173 / 200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (623261053 / 1000000000) (311630527 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (232476372769 / 200000000000) (116238186571 / 100000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(173 / 200)
  have hx56 : Bounds (-173 / 200) (-173 / 200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((173 / 200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (27 / 200) (27 / 200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(173 / 200)
  have hx58 : Bounds (27 / 200) (27 / 200) x58 := by
    exact hx57
  let x59 : ℝ := -(173 / 200)
  have hx59 : Bounds (-173 / 200) (-173 / 200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((173 / 200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (27 / 200) (27 / 200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(173 / 200)
  have hx61 : Bounds (27 / 200) (27 / 200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1001240251 / 500000000) (-2002480499 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-27033486777 / 100000000000) (-54066973473 / 200000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (35681879843 / 40000000000) (178409399669 / 200000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (446023498037 / 1000000000000) (446023499173 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (446023498037 / 1000000000000) (446023499173 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-446023499173 / 1000000000000) (-446023498037 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (247123680827 / 1000000000000) (247123682963 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (247123680827 / 1000000000000) (247123682963 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (173 / 200)
  have hx71 : Bounds (247123680827 / 1000000000000) (247123682963 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(11053 / 12800)
  have hx73 : Bounds (23853 / 12800) (23853 / 12800) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11053 / 12800) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(11053 / 12800)
  have hx74 : Bounds (23853 / 12800) (23853 / 12800) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11053 / 12800) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (77808103 / 125000000) (24898593 / 40000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (36249153923 / 31250000000) (1159972927401 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(11053 / 12800)
  have hx77 : Bounds (-11053 / 12800) (-11053 / 12800) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11053 / 12800) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1747 / 12800) (1747 / 12800) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(11053 / 12800)
  have hx79 : Bounds (1747 / 12800) (1747 / 12800) x79 := by
    exact hx78
  let x80 : ℝ := -(11053 / 12800)
  have hx80 : Bounds (-11053 / 12800) (-11053 / 12800) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11053 / 12800) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1747 / 12800) (1747 / 12800) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(11053 / 12800)
  have hx82 : Bounds (1747 / 12800) (1747 / 12800) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1991545141 / 1000000000) (-995772569 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-135907396927 / 500000000000) (-67953698361 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (444079065841 / 500000000000) (888158133957 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (444079065841 / 1000000000000) (444079066979 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (444079065841 / 1000000000000) (444079066979 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-444079066979 / 1000000000000) (-444079065841 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (249068113021 / 1000000000000) (249068115159 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (249068113021 / 1000000000000) (249068115159 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (11053 / 12800)
  have hx92 : Bounds (249068113021 / 1000000000000) (249068115159 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (247123680827 / 1000000000000) (249068115159 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (123561840413 / 1000000000000) (6226702879 / 50000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (123561840413 / 1000000000000) (6226702879 / 50000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(945787 / 1000000)
  have hx98 : Bounds (1945787 / 1000000) (1945787 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((945787 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(945787 / 1000000)
  have hx99 : Bounds (1945787 / 1000000) (1945787 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((945787 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (332833261 / 500000000) (665666523 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (647622632421 / 500000000000) (1295245266789 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(945787 / 1000000)
  have hx102 : Bounds (-945787 / 1000000) (-945787 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((945787 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (54213 / 1000000) (54213 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(945787 / 1000000)
  have hx104 : Bounds (54213 / 1000000) (54213 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(945787 / 1000000)
  have hx105 : Bounds (-945787 / 1000000) (-945787 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((945787 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (54213 / 1000000) (54213 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(945787 / 1000000)
  have hx107 : Bounds (54213 / 1000000) (54213 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-2914834549 / 1000000000) (-182177159 / 62500000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-31604385081 / 200000000000) (-158021925133 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1137223339437 / 1000000000000) (142152917707 / 125000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (284305834859 / 500000000000) (142152917707 / 250000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (284305834859 / 500000000000) (142152917707 / 250000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-142152917707 / 250000000000) (-284305834859 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (31133877293 / 250000000000) (62267755641 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (31133877293 / 250000000000) (62267755641 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (945787 / 1000000)
  have hx117 : Bounds (31133877293 / 250000000000) (62267755641 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(946331 / 1000000)
  have hx119 : Bounds (1946331 / 1000000) (1946331 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((946331 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(946331 / 1000000)
  have hx120 : Bounds (1946331 / 1000000) (1946331 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((946331 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (665946061 / 1000000000) (332973031 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (324037865713 / 250000000000) (1296151464799 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(946331 / 1000000)
  have hx123 : Bounds (-946331 / 1000000) (-946331 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((946331 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (53669 / 1000000) (53669 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(946331 / 1000000)
  have hx125 : Bounds (53669 / 1000000) (53669 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(946331 / 1000000)
  have hx126 : Bounds (-946331 / 1000000) (-946331 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((946331 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (53669 / 1000000) (53669 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(946331 / 1000000)
  have hx128 : Bounds (53669 / 1000000) (53669 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-182807483 / 62500000) (-2924919723 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-156977516883 / 1000000000000) (-156977516613 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1139173945969 / 1000000000000) (569586974093 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (71198371623 / 125000000000) (569586974093 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (71198371623 / 125000000000) (569586974093 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-569586974093 / 1000000000000) (-71198371623 / 125000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (123560205907 / 1000000000000) (7722513001 / 62500000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (123560205907 / 1000000000000) (7722513001 / 62500000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (946331 / 1000000)
  have hx138 : Bounds (123560205907 / 1000000000000) (7722513001 / 62500000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (945787 / 1000000) (946331 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (946331 / 1000000) ≤ (7722513001 / 62500000000) := hx138.2
      have h2 : (123561840413 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (6226702879 / 50000000000) := hx96.2
      have h2 : (31133877293 / 250000000000) ≤ biasE (945787 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1072386058981 / 1000000000000) (13415503291 / 12500000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (3312649877 / 25000000000) (26730992949 / 200000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (3312649877 / 25000000000) (26730992949 / 200000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(94481 / 100000)
  have hx143 : Bounds (194481 / 100000) (194481 / 100000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((94481 / 100000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(94481 / 100000)
  have hx144 : Bounds (194481 / 100000) (194481 / 100000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((94481 / 100000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (133032857 / 200000000) (332582143 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (129361815311 / 100000000000) (80851134691 / 62500000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(94481 / 100000)
  have hx147 : Bounds (-94481 / 100000) (-94481 / 100000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((94481 / 100000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (5519 / 100000) (5519 / 100000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(94481 / 100000)
  have hx149 : Bounds (5519 / 100000) (5519 / 100000) x149 := by
    exact hx148
  let x150 : ℝ := -(94481 / 100000)
  have hx150 : Bounds (-94481 / 100000) (-94481 / 100000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((94481 / 100000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (5519 / 100000) (5519 / 100000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(94481 / 100000)
  have hx152 : Bounds (5519 / 100000) (5519 / 100000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-45265211 / 15625000) (-2896973499 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-79941983843 / 500000000000) (-159883967409 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (70858386589 / 62500000000) (1133734187647 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (70858386589 / 125000000000) (8857298341 / 15625000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (70858386589 / 125000000000) (8857298341 / 15625000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-8857298341 / 15625000000) (-70858386589 / 125000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (3946252693 / 31250000000) (3946252759 / 31250000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (3946252693 / 31250000000) (3946252759 / 31250000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (94481 / 100000)
  have hx162 : Bounds (3946252693 / 31250000000) (3946252759 / 31250000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(472689 / 500000)
  have hx164 : Bounds (972689 / 500000) (972689 / 500000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472689 / 500000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(472689 / 500000)
  have hx165 : Bounds (972689 / 500000) (972689 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472689 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (332728151 / 500000000) (665456303 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (80910253117 / 62500000000) (647282025909 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(472689 / 500000)
  have hx168 : Bounds (-472689 / 500000) (-472689 / 500000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472689 / 500000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (27311 / 500000) (27311 / 500000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(472689 / 500000)
  have hx170 : Bounds (27311 / 500000) (27311 / 500000) x170 := by
    exact hx169
  let x171 : ℝ := -(472689 / 500000)
  have hx171 : Bounds (-472689 / 500000) (-472689 / 500000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472689 / 500000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (27311 / 500000) (27311 / 500000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(472689 / 500000)
  have hx173 : Bounds (27311 / 500000) (27311 / 500000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-2907318549 / 1000000000) (-181707409 / 62500000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-19850444223 / 125000000000) (-15880355351 / 100000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (141970062011 / 125000000000) (283940124577 / 250000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (141970062011 / 250000000000) (283940124577 / 500000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (141970062011 / 250000000000) (283940124577 / 500000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-283940124577 / 500000000000) (-141970062011 / 250000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (62633465423 / 500000000000) (31316733239 / 250000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (62633465423 / 500000000000) (31316733239 / 250000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (472689 / 500000)
  have hx183 : Bounds (62633465423 / 500000000000) (31316733239 / 250000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(94481 / 100000)
  have hx184 : Bounds (125192989211 / 1000000000000) (126278547241 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((94481 / 100000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(472689 / 500000)
  have hx185 : Bounds (15658531577 / 125000000000) (126354463261 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((472689 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (94481 / 100000) (472689 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (94481 / 100000) ≤ (126278547241 / 1000000000000) := hx184.2
      have h2 : (3946252693 / 31250000000) ≤ biasE (94481 / 100000) := hx162.1
      linarith
    · have h1 : biasE (472689 / 500000) ≤ (31316733239 / 250000000000) := hx183.2
      have h2 : (15658531577 / 125000000000) ≤ x141 * (472689 / 500000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1945787 / 1000000) (1946331 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-946331 / 1000000) (-945787 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (53669 / 1000000) (54213 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (53669 / 1000000) (54213 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (2305720030251 / 125000000000) (3726546050793 / 200000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (2243220030251 / 62500000000) (3626546050793 / 100000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (2243220030251 / 62500000000) (3626546050793 / 100000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1790250533 / 500000000) (359086579 / 100000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1790250533 / 1000000000) (359086579 / 200000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1790250533 / 1000000000) (359086579 / 200000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (194481 / 100000) (972689 / 500000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-472689 / 500000) (-94481 / 100000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (27311 / 500000) (5519 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (27311 / 500000) (5519 / 100000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (18119224497191 / 1000000000000) (2288455201201 / 125000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (17619224497191 / 500000000000) (2225955201201 / 62500000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (17619224497191 / 500000000000) (2225955201201 / 62500000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (445267223 / 125000000) (893193713 / 250000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (445267223 / 250000000) (893193713 / 500000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (445267223 / 250000000) (893193713 / 500000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (18443137701 / 62500000000) (7439390593 / 25000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (123561840413 / 500000000000) (6226702879 / 25000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-6226702879 / 25000000000) (-123561840413 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (5752761007 / 125000000000) (25225971447 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (5752761007 / 125000000000) (25225971447 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (846597840427 / 500000000000) (1699073806959 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1699073806959 / 1000000000000) (-846597840427 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-1653051718903 / 1000000000000) (-41068593449 / 25000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-1653051718903 / 1000000000000) (-41068593449 / 25000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1659524854721 / 1000000000000) (333161254949 / 200000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (3236567909 / 500000000000) (4612507357 / 200000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (27 / 800) (1747 / 51200) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (27 / 800) ≤ m → m ≤ (1747 / 51200) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1747 / 51200) (883 / 25600) m) :
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
  have hx0 : Bounds (1747 / 25600) (883 / 12800) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-883 / 12800) (-1747 / 25600) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (11917 / 12800) (23853 / 25600) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (11917 / 12800) (23853 / 25600) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1747 / 12800) (883 / 6400) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-883 / 6400) (-1747 / 12800) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (5517 / 6400) (11053 / 12800) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (5517 / 6400) (11053 / 12800) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(23853 / 25600)
  have hx9 : Bounds (49453 / 25600) (49453 / 25600) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23853 / 25600) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(23853 / 25600)
  have hx10 : Bounds (49453 / 25600) (49453 / 25600) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23853 / 25600) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (164607593 / 250000000) (658430373 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (635964007549 / 500000000000) (1271928017031 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(23853 / 25600)
  have hx13 : Bounds (-23853 / 25600) (-23853 / 25600) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23853 / 25600) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1747 / 25600) (1747 / 25600) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(23853 / 25600)
  have hx15 : Bounds (1747 / 25600) (1747 / 25600) x15 := by
    exact hx14
  let x16 : ℝ := -(23853 / 25600)
  have hx16 : Bounds (-23853 / 25600) (-23853 / 25600) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23853 / 25600) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1747 / 25600) (1747 / 25600) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(23853 / 25600)
  have hx18 : Bounds (1747 / 25600) (1747 / 25600) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1342346161 / 500000000) (-1342346159 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-91604638409 / 500000000000) (-1431322473 / 7812500000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (27217968457 / 25000000000) (1088718740487 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (27217968457 / 50000000000) (136089842561 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (27217968457 / 50000000000) (136089842561 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-136089842561 / 250000000000) (-27217968457 / 50000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (37196952439 / 250000000000) (7439390593 / 50000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (37196952439 / 250000000000) (7439390593 / 50000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (23853 / 25600)
  have hx28 : Bounds (37196952439 / 250000000000) (7439390593 / 50000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(11917 / 12800)
  have hx30 : Bounds (24717 / 12800) (24717 / 12800) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11917 / 12800) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(11917 / 12800)
  have hx31 : Bounds (24717 / 12800) (24717 / 12800) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11917 / 12800) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (131609219 / 200000000) (41127881 / 62500000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (254139458283 / 200000000000) (1270697293347 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(11917 / 12800)
  have hx34 : Bounds (-11917 / 12800) (-11917 / 12800) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11917 / 12800) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (883 / 12800) (883 / 12800) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(11917 / 12800)
  have hx36 : Bounds (883 / 12800) (883 / 12800) x36 := by
    exact hx35
  let x37 : ℝ := -(11917 / 12800)
  have hx37 : Bounds (-11917 / 12800) (-11917 / 12800) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11917 / 12800) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (883 / 12800) (883 / 12800) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(11917 / 12800)
  have hx39 : Bounds (883 / 12800) (883 / 12800) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-2673875251 / 1000000000) (-2673875247 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-184455613019 / 1000000000000) (-92227806371 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (271560419599 / 250000000000) (217248336121 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (271560419599 / 500000000000) (543120840303 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (271560419599 / 500000000000) (543120840303 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-543120840303 / 1000000000000) (-271560419599 / 500000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (150026339697 / 1000000000000) (75013170901 / 500000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (150026339697 / 1000000000000) (75013170901 / 500000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (11917 / 12800)
  have hx49 : Bounds (150026339697 / 1000000000000) (75013170901 / 500000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (37196952439 / 250000000000) (75013170901 / 500000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(11053 / 12800)
  have hx52 : Bounds (23853 / 12800) (23853 / 12800) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11053 / 12800) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(11053 / 12800)
  have hx53 : Bounds (23853 / 12800) (23853 / 12800) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11053 / 12800) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (77808103 / 125000000) (24898593 / 40000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (36249153923 / 31250000000) (1159972927401 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(11053 / 12800)
  have hx56 : Bounds (-11053 / 12800) (-11053 / 12800) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11053 / 12800) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1747 / 12800) (1747 / 12800) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(11053 / 12800)
  have hx58 : Bounds (1747 / 12800) (1747 / 12800) x58 := by
    exact hx57
  let x59 : ℝ := -(11053 / 12800)
  have hx59 : Bounds (-11053 / 12800) (-11053 / 12800) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11053 / 12800) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1747 / 12800) (1747 / 12800) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(11053 / 12800)
  have hx61 : Bounds (1747 / 12800) (1747 / 12800) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1991545141 / 1000000000) (-995772569 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-135907396927 / 500000000000) (-67953698361 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (444079065841 / 500000000000) (888158133957 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (444079065841 / 1000000000000) (444079066979 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (444079065841 / 1000000000000) (444079066979 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-444079066979 / 1000000000000) (-444079065841 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (249068113021 / 1000000000000) (249068115159 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (249068113021 / 1000000000000) (249068115159 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (11053 / 12800)
  have hx71 : Bounds (249068113021 / 1000000000000) (249068115159 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(5517 / 6400)
  have hx73 : Bounds (11917 / 6400) (11917 / 6400) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5517 / 6400) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(5517 / 6400)
  have hx74 : Bounds (11917 / 6400) (11917 / 6400) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5517 / 6400) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (621667961 / 1000000000) (310833981 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (231513034101 / 200000000000) (72347823273 / 62500000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(5517 / 6400)
  have hx77 : Bounds (-5517 / 6400) (-5517 / 6400) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5517 / 6400) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (883 / 6400) (883 / 6400) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(5517 / 6400)
  have hx79 : Bounds (883 / 6400) (883 / 6400) x79 := by
    exact hx78
  let x80 : ℝ := -(5517 / 6400)
  have hx80 : Bounds (-5517 / 6400) (-5517 / 6400) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5517 / 6400) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (883 / 6400) (883 / 6400) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(5517 / 6400)
  have hx82 : Bounds (883 / 6400) (883 / 6400) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-198072807 / 100000000) (-1980728067 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-68319643977 / 250000000000) (-273278575493 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (884286594597 / 1000000000000) (282971711 / 320000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (221071648649 / 500000000000) (221071649219 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (221071648649 / 500000000000) (221071649219 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-221071649219 / 500000000000) (-221071648649 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (125501940781 / 500000000000) (125501941851 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (125501940781 / 500000000000) (125501941851 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (5517 / 6400)
  have hx92 : Bounds (125501940781 / 500000000000) (125501941851 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (249068113021 / 1000000000000) (125501941851 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (12453405651 / 100000000000) (125501941851 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (12453405651 / 100000000000) (125501941851 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(472623 / 500000)
  have hx98 : Bounds (972623 / 500000) (972623 / 500000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472623 / 500000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(472623 / 500000)
  have hx99 : Bounds (972623 / 500000) (972623 / 500000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472623 / 500000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (665388447 / 1000000000) (20793389 / 31250000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (323586053743 / 250000000000) (1294344216919 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(472623 / 500000)
  have hx102 : Bounds (-472623 / 500000) (-472623 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472623 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (27377 / 500000) (27377 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(472623 / 500000)
  have hx104 : Bounds (27377 / 500000) (27377 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := -(472623 / 500000)
  have hx105 : Bounds (-472623 / 500000) (-472623 / 500000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472623 / 500000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (27377 / 500000) (27377 / 500000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(472623 / 500000)
  have hx107 : Bounds (27377 / 500000) (27377 / 500000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-363113107 / 125000000) (-2904904851 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-79527580243 / 500000000000) (-159055160211 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (567644527243 / 500000000000) (283822264177 / 250000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (567644527243 / 1000000000000) (283822264177 / 500000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (567644527243 / 1000000000000) (283822264177 / 500000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-283822264177 / 500000000000) (-567644527243 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (62751325823 / 500000000000) (125502653757 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (62751325823 / 500000000000) (125502653757 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (472623 / 500000)
  have hx117 : Bounds (62751325823 / 500000000000) (125502653757 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(236447 / 250000)
  have hx119 : Bounds (486447 / 250000) (486447 / 250000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((236447 / 250000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(236447 / 250000)
  have hx120 : Bounds (486447 / 250000) (486447 / 250000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((236447 / 250000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (166416759 / 250000000) (665667037 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (323811732661 / 250000000000) (1295246932591 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(236447 / 250000)
  have hx123 : Bounds (-236447 / 250000) (-236447 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((236447 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (13553 / 250000) (13553 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(236447 / 250000)
  have hx125 : Bounds (13553 / 250000) (13553 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := -(236447 / 250000)
  have hx126 : Bounds (-236447 / 250000) (-236447 / 250000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((236447 / 250000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (13553 / 250000) (13553 / 250000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(236447 / 250000)
  have hx128 : Bounds (13553 / 250000) (13553 / 250000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-582970599 / 200000000) (-291485299 / 100000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-31604002113 / 200000000000) (-158020010293 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1137226920079 / 1000000000000) (568613461149 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (568613460039 / 1000000000000) (568613461149 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (568613460039 / 1000000000000) (568613461149 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-568613461149 / 1000000000000) (-568613460039 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (124533718851 / 1000000000000) (124533720961 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (124533718851 / 1000000000000) (124533720961 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (236447 / 250000)
  have hx138 : Bounds (124533718851 / 1000000000000) (124533720961 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (472623 / 500000) (236447 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (236447 / 250000) ≤ (124533720961 / 1000000000000) := hx138.2
      have h2 : (12453405651 / 100000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (125501941851 / 1000000000000) := hx96.2
      have h2 : (62751325823 / 500000000000) ≤ biasE (472623 / 500000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1073240263279 / 1000000000000) (67130989343 / 62500000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (26730992719 / 200000000000) (26960222467 / 200000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (26730992719 / 200000000000) (26960222467 / 200000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(236061 / 250000)
  have hx143 : Bounds (486061 / 250000) (486061 / 250000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((236061 / 250000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(236061 / 250000)
  have hx144 : Bounds (486061 / 250000) (486061 / 250000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((236061 / 250000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (166218303 / 250000000) (664873213 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1292675753191 / 1000000000000) (10099029337 / 7812500000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(236061 / 250000)
  have hx147 : Bounds (-236061 / 250000) (-236061 / 250000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((236061 / 250000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (13939 / 250000) (13939 / 250000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(236061 / 250000)
  have hx149 : Bounds (13939 / 250000) (13939 / 250000) x149 := by
    exact hx148
  let x150 : ℝ := -(236061 / 250000)
  have hx150 : Bounds (-236061 / 250000) (-236061 / 250000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((236061 / 250000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (13939 / 250000) (13939 / 250000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(236061 / 250000)
  have hx152 : Bounds (13939 / 250000) (13939 / 250000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-2886770253 / 1000000000) (-360846281 / 125000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-160954762227 / 1000000000000) (-160954761947 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (282930247741 / 250000000000) (1131720993189 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (282930247741 / 500000000000) (113172099319 / 200000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (282930247741 / 500000000000) (113172099319 / 200000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-113172099319 / 200000000000) (-282930247741 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (25457336681 / 200000000000) (63643342759 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (25457336681 / 200000000000) (63643342759 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (236061 / 250000)
  have hx162 : Bounds (25457336681 / 200000000000) (63643342759 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(944811 / 1000000)
  have hx164 : Bounds (1944811 / 1000000) (1944811 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((944811 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(944811 / 1000000)
  have hx165 : Bounds (1944811 / 1000000) (1944811 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((944811 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (51966 / 78125) (665164801 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (323404954963 / 250000000000) (646809910899 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(944811 / 1000000)
  have hx168 : Bounds (-944811 / 1000000) (-944811 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((944811 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (55189 / 1000000) (55189 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(944811 / 1000000)
  have hx170 : Bounds (55189 / 1000000) (55189 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(944811 / 1000000)
  have hx171 : Bounds (-944811 / 1000000) (-944811 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((944811 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (55189 / 1000000) (55189 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(944811 / 1000000)
  have hx173 : Bounds (55189 / 1000000) (55189 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-2896991623 / 1000000000) (-1448495809 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-79941035341 / 500000000000) (-31976414081 / 200000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (113373774917 / 100000000000) (1133737751393 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (113373774917 / 200000000000) (566868875697 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (113373774917 / 200000000000) (566868875697 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-566868875697 / 1000000000000) (-113373774917 / 200000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (126278304303 / 1000000000000) (25255661283 / 200000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (126278304303 / 1000000000000) (25255661283 / 200000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (944811 / 1000000)
  have hx183 : Bounds (126278304303 / 1000000000000) (25255661283 / 200000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(236061 / 250000)
  have hx184 : Bounds (31550724361 / 250000000000) (31821285379 / 250000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((236061 / 250000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(944811 / 1000000)
  have hx185 : Bounds (126278679809 / 1000000000000) (127361573747 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((944811 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (236061 / 250000) (944811 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (236061 / 250000) ≤ (31821285379 / 250000000000) := hx184.2
      have h2 : (25457336681 / 200000000000) ≤ biasE (236061 / 250000) := hx162.1
      linarith
    · have h1 : biasE (944811 / 1000000) ≤ (25255661283 / 200000000000) := hx183.2
      have h2 : (126278679809 / 1000000000000) ≤ x141 * (944811 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (972623 / 500000) (486447 / 250000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-236447 / 250000) (-472623 / 500000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (13553 / 250000) (27377 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (13553 / 250000) (27377 / 500000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (3652701172517 / 200000000000) (4611525123589 / 250000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (3552701172517 / 100000000000) (4486525123589 / 125000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (3552701172517 / 100000000000) (4486525123589 / 125000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1785146649 / 500000000) (111891251 / 31250000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1785146649 / 1000000000) (111891251 / 62500000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1785146649 / 1000000000) (111891251 / 62500000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (486061 / 250000) (1944811 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-944811 / 1000000) (-236061 / 250000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (55189 / 1000000) (13939 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (55189 / 1000000) (13939 / 250000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (4483822368893 / 250000000000) (18119552809437 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (4358822368893 / 125000000000) (17619552809437 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (4358822368893 / 125000000000) (17619552809437 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (177582173 / 50000000) (445269553 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (177582173 / 100000000) (445269553 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (177582173 / 100000000) (445269553 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (37196952439 / 125000000000) (75013170901 / 250000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (12453405651 / 50000000000) (125501941851 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-125501941851 / 500000000000) (-12453405651 / 50000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (4657173581 / 100000000000) (6373071323 / 125000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (4657173581 / 100000000000) (6373071323 / 125000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (84370136469 / 50000000000) (1693206440013 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1693206440013 / 1000000000000) (-84370136469 / 50000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-1646634704203 / 1000000000000) (-409104539699 / 250000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-1646634704203 / 1000000000000) (-409104539699 / 250000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (413329444461 / 250000000000) (331906707741 / 200000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (6683073641 / 1000000000000) (23115379909 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1747 / 51200) (883 / 25600) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1747 / 51200) ≤ m → m ≤ (883 / 25600) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (883 / 25600) (357 / 10240) m) :
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
  have hx0 : Bounds (883 / 12800) (357 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-357 / 5120) (-883 / 12800) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (4763 / 5120) (11917 / 12800) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (4763 / 5120) (11917 / 12800) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (883 / 6400) (357 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-357 / 2560) (-883 / 6400) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2203 / 2560) (5517 / 6400) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (2203 / 2560) (5517 / 6400) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(11917 / 12800)
  have hx9 : Bounds (24717 / 12800) (24717 / 12800) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11917 / 12800) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(11917 / 12800)
  have hx10 : Bounds (24717 / 12800) (24717 / 12800) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11917 / 12800) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (131609219 / 200000000) (41127881 / 62500000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (254139458283 / 200000000000) (1270697293347 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(11917 / 12800)
  have hx13 : Bounds (-11917 / 12800) (-11917 / 12800) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11917 / 12800) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (883 / 12800) (883 / 12800) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(11917 / 12800)
  have hx15 : Bounds (883 / 12800) (883 / 12800) x15 := by
    exact hx14
  let x16 : ℝ := -(11917 / 12800)
  have hx16 : Bounds (-11917 / 12800) (-11917 / 12800) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11917 / 12800) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (883 / 12800) (883 / 12800) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(11917 / 12800)
  have hx18 : Bounds (883 / 12800) (883 / 12800) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-2673875251 / 1000000000) (-2673875247 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-184455613019 / 1000000000000) (-92227806371 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (271560419599 / 250000000000) (217248336121 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (271560419599 / 500000000000) (543120840303 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (271560419599 / 500000000000) (543120840303 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-543120840303 / 1000000000000) (-271560419599 / 500000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (150026339697 / 1000000000000) (75013170901 / 500000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (150026339697 / 1000000000000) (75013170901 / 500000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (11917 / 12800)
  have hx28 : Bounds (150026339697 / 1000000000000) (75013170901 / 500000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(4763 / 5120)
  have hx30 : Bounds (9883 / 5120) (9883 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4763 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(4763 / 5120)
  have hx31 : Bounds (9883 / 5120) (9883 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4763 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (65766167 / 100000000) (657661671 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (634733426231 / 500000000000) (634733427197 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(4763 / 5120)
  have hx34 : Bounds (-4763 / 5120) (-4763 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4763 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (357 / 5120) (357 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(4763 / 5120)
  have hx36 : Bounds (357 / 5120) (357 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(4763 / 5120)
  have hx37 : Bounds (-4763 / 5120) (-4763 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4763 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (357 / 5120) (357 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(4763 / 5120)
  have hx39 : Bounds (357 / 5120) (357 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1331586969 / 500000000) (-1331586967 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-185693964037 / 1000000000000) (-185693963757 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (43350915537 / 40000000000) (1083772890637 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (135471611053 / 250000000000) (541886445319 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (135471611053 / 250000000000) (541886445319 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-541886445319 / 1000000000000) (-135471611053 / 250000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (151260734681 / 1000000000000) (37815184197 / 250000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (151260734681 / 1000000000000) (37815184197 / 250000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (4763 / 5120)
  have hx49 : Bounds (151260734681 / 1000000000000) (37815184197 / 250000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (150026339697 / 1000000000000) (37815184197 / 250000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(5517 / 6400)
  have hx52 : Bounds (11917 / 6400) (11917 / 6400) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5517 / 6400) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(5517 / 6400)
  have hx53 : Bounds (11917 / 6400) (11917 / 6400) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5517 / 6400) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (621667961 / 1000000000) (310833981 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (231513034101 / 200000000000) (72347823273 / 62500000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(5517 / 6400)
  have hx56 : Bounds (-5517 / 6400) (-5517 / 6400) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5517 / 6400) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (883 / 6400) (883 / 6400) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(5517 / 6400)
  have hx58 : Bounds (883 / 6400) (883 / 6400) x58 := by
    exact hx57
  let x59 : ℝ := -(5517 / 6400)
  have hx59 : Bounds (-5517 / 6400) (-5517 / 6400) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5517 / 6400) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (883 / 6400) (883 / 6400) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(5517 / 6400)
  have hx61 : Bounds (883 / 6400) (883 / 6400) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-198072807 / 100000000) (-1980728067 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-68319643977 / 250000000000) (-273278575493 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (884286594597 / 1000000000000) (282971711 / 320000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (221071648649 / 500000000000) (221071649219 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (221071648649 / 500000000000) (221071649219 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-221071649219 / 500000000000) (-221071648649 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (125501940781 / 500000000000) (125501941851 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (125501940781 / 500000000000) (125501941851 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (5517 / 6400)
  have hx71 : Bounds (125501940781 / 500000000000) (125501941851 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2203 / 2560)
  have hx73 : Bounds (4763 / 2560) (4763 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2203 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2203 / 2560)
  have hx74 : Bounds (4763 / 2560) (4763 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2203 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (620870463 / 1000000000) (9701101 / 15625000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (577579299857 / 500000000000) (46206344063 / 40000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2203 / 2560)
  have hx77 : Bounds (-2203 / 2560) (-2203 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2203 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (357 / 2560) (357 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2203 / 2560)
  have hx79 : Bounds (357 / 2560) (357 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(2203 / 2560)
  have hx80 : Bounds (-2203 / 2560) (-2203 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2203 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (357 / 2560) (357 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2203 / 2560)
  have hx82 : Bounds (357 / 2560) (357 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1970026757 / 1000000000) (-985013377 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-137363193799 / 500000000000) (-137363193589 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (220108053029 / 250000000000) (880432214397 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (220108053029 / 500000000000) (440216107199 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (220108053029 / 500000000000) (440216107199 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-440216107199 / 1000000000000) (-220108053029 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (252931072801 / 1000000000000) (126465537471 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (252931072801 / 1000000000000) (126465537471 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2203 / 2560)
  have hx92 : Bounds (252931072801 / 1000000000000) (126465537471 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (125501940781 / 500000000000) (126465537471 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (125501940781 / 1000000000000) (126465537471 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (125501940781 / 1000000000000) (126465537471 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(188941 / 200000)
  have hx98 : Bounds (388941 / 200000) (388941 / 200000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((188941 / 200000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(188941 / 200000)
  have hx99 : Bounds (388941 / 200000) (388941 / 200000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((188941 / 200000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (332555147 / 500000000) (133022059 / 200000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1293443314293 / 1000000000000) (646721658119 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(188941 / 200000)
  have hx102 : Bounds (-188941 / 200000) (-188941 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((188941 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (11059 / 200000) (11059 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(188941 / 200000)
  have hx104 : Bounds (11059 / 200000) (11059 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := -(188941 / 200000)
  have hx105 : Bounds (-188941 / 200000) (-188941 / 200000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((188941 / 200000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (11059 / 200000) (11059 / 200000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(188941 / 200000)
  have hx107 : Bounds (11059 / 200000) (11059 / 200000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-2895072793 / 1000000000) (-723768197 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-160083050089 / 1000000000000) (-40020762453 / 250000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (283340066051 / 250000000000) (566680133213 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (283340066051 / 500000000000) (566680133213 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (283340066051 / 500000000000) (566680133213 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-566680133213 / 1000000000000) (-283340066051 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (126467046787 / 1000000000000) (63233524449 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (126467046787 / 1000000000000) (63233524449 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (188941 / 200000)
  have hx117 : Bounds (126467046787 / 1000000000000) (63233524449 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(945247 / 1000000)
  have hx119 : Bounds (1945247 / 1000000) (1945247 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((945247 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(945247 / 1000000)
  have hx120 : Bounds (1945247 / 1000000) (1945247 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((945247 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (665388961 / 1000000000) (332694481 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (647172940109 / 500000000000) (323586470541 / 250000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(945247 / 1000000)
  have hx123 : Bounds (-945247 / 1000000) (-945247 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((945247 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (54753 / 1000000) (54753 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(945247 / 1000000)
  have hx125 : Bounds (54753 / 1000000) (54753 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(945247 / 1000000)
  have hx126 : Bounds (-945247 / 1000000) (-945247 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((945247 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (54753 / 1000000) (54753 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(945247 / 1000000)
  have hx128 : Bounds (54753 / 1000000) (54753 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-36311539 / 12500000) (-580984623 / 200000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-15905325559 / 100000000000) (-31810651063 / 200000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (283823156157 / 250000000000) (1135292626849 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (283823156157 / 500000000000) (22705852537 / 40000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (283823156157 / 500000000000) (22705852537 / 40000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-22705852537 / 40000000000) (-283823156157 / 500000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (5020034663 / 40000000000) (62750434343 / 500000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (5020034663 / 40000000000) (62750434343 / 500000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (945247 / 1000000)
  have hx138 : Bounds (5020034663 / 40000000000) (62750434343 / 500000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (188941 / 200000) (945247 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (945247 / 1000000) ≤ (62750434343 / 500000000000) := hx138.2
      have h2 : (125501940781 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (126465537471 / 1000000000000) := hx96.2
      have h2 : (126467046787 / 1000000000000) ≤ biasE (188941 / 200000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1074095829487 / 1000000000000) (537476380433 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (26960222237 / 200000000000) (135944478659 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (26960222237 / 200000000000) (135944478659 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(943679 / 1000000)
  have hx143 : Bounds (1943679 / 1000000) (1943679 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((943679 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(943679 / 1000000)
  have hx144 : Bounds (1943679 / 1000000) (1943679 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((943679 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (83072821 / 125000000) (664582569 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1291735181187 / 1000000000000) (322933795783 / 250000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(943679 / 1000000)
  have hx147 : Bounds (-943679 / 1000000) (-943679 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((943679 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (56321 / 1000000) (56321 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(943679 / 1000000)
  have hx149 : Bounds (56321 / 1000000) (56321 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(943679 / 1000000)
  have hx150 : Bounds (-943679 / 1000000) (-943679 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((943679 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (56321 / 1000000) (56321 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(943679 / 1000000)
  have hx152 : Bounds (56321 / 1000000) (56321 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-1438343907 / 500000000) (-2876687809 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-162017934373 / 1000000000000) (-16201793409 / 100000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (564858623407 / 500000000000) (564858624521 / 500000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (564858623407 / 1000000000000) (564858624521 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (564858623407 / 1000000000000) (564858624521 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-564858624521 / 1000000000000) (-564858623407 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (128288555479 / 1000000000000) (128288557593 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (128288555479 / 1000000000000) (128288557593 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (943679 / 1000000)
  have hx162 : Bounds (128288555479 / 1000000000000) (128288557593 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(188849 / 200000)
  have hx164 : Bounds (388849 / 200000) (388849 / 200000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((188849 / 200000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(188849 / 200000)
  have hx165 : Bounds (388849 / 200000) (388849 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((188849 / 200000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (332436863 / 500000000) (664873727 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (646338708703 / 500000000000) (161584677419 / 125000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(188849 / 200000)
  have hx168 : Bounds (-188849 / 200000) (-188849 / 200000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((188849 / 200000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (11151 / 200000) (11151 / 200000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(188849 / 200000)
  have hx170 : Bounds (11151 / 200000) (11151 / 200000) x170 := by
    exact hx169
  let x171 : ℝ := -(188849 / 200000)
  have hx171 : Bounds (-188849 / 200000) (-188849 / 200000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((188849 / 200000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (11151 / 200000) (11151 / 200000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(188849 / 200000)
  have hx173 : Bounds (11151 / 200000) (11151 / 200000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-2886788189 / 1000000000) (-360848523 / 125000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-80476437739 / 500000000000) (-80476437599 / 500000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (141465567741 / 125000000000) (565862272077 / 500000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (141465567741 / 250000000000) (565862272077 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (141465567741 / 250000000000) (565862272077 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-565862272077 / 1000000000000) (-141465567741 / 250000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (127284907923 / 1000000000000) (31821227509 / 250000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (127284907923 / 1000000000000) (31821227509 / 250000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (188849 / 200000)
  have hx183 : Bounds (127284907923 / 1000000000000) (31821227509 / 250000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(943679 / 1000000)
  have hx184 : Bounds (127208977801 / 1000000000000) (128287949677 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((943679 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(188849 / 200000)
  have hx185 : Bounds (12728527523 / 100000000000) (32091223563 / 250000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((188849 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (943679 / 1000000) (188849 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (943679 / 1000000) ≤ (128287949677 / 1000000000000) := hx184.2
      have h2 : (128288555479 / 1000000000000) ≤ biasE (943679 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (188849 / 200000) ≤ (31821227509 / 250000000000) := hx183.2
      have h2 : (12728527523 / 100000000000) ≤ x141 * (188849 / 200000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (388941 / 200000) (1945247 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-945247 / 1000000) (-188941 / 200000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (54753 / 1000000) (11059 / 200000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (54753 / 1000000) (11059 / 200000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (904240889773 / 50000000000) (4565959856081 / 250000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (879240889773 / 25000000000) (4440959856081 / 125000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (879240889773 / 25000000000) (4440959856081 / 125000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1780091541 / 500000000) (3570312081 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1780091541 / 1000000000) (3570312081 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1780091541 / 1000000000) (3570312081 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1943679 / 1000000) (388849 / 200000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-188849 / 200000) (-943679 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (11151 / 200000) (56321 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (11151 / 200000) (56321 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (8877683279771 / 500000000000) (17935611155951 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (8627683279771 / 250000000000) (17435611155951 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (8627683279771 / 250000000000) (17435611155951 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (3541270377 / 1000000000) (887915479 / 250000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (3541270377 / 2000000000) (887915479 / 500000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (3541270377 / 2000000000) (887915479 / 500000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (150026339697 / 500000000000) (37815184197 / 125000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (125501940781 / 500000000000) (126465537471 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-126465537471 / 500000000000) (-125501940781 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (11780401113 / 250000000000) (25758796007 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (11780401113 / 250000000000) (25758796007 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (42041534481 / 25000000000) (337482678363 / 200000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-337482678363 / 200000000000) (-42041534481 / 25000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-1640291787363 / 1000000000000) (-815071893613 / 500000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-1640291787363 / 1000000000000) (-815071893613 / 500000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (411793720841 / 250000000000) (1653326369257 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (6883096001 / 1000000000000) (23182582031 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (883 / 25600) (357 / 10240) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (883 / 25600) ≤ m → m ≤ (357 / 10240) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (357 / 10240) (451 / 12800) m) :
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
  have hx0 : Bounds (357 / 5120) (451 / 6400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-451 / 6400) (-357 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (5949 / 6400) (4763 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (5949 / 6400) (4763 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (357 / 2560) (451 / 3200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-451 / 3200) (-357 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2749 / 3200) (2203 / 2560) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (2749 / 3200) (2203 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(4763 / 5120)
  have hx9 : Bounds (9883 / 5120) (9883 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4763 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(4763 / 5120)
  have hx10 : Bounds (9883 / 5120) (9883 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4763 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (65766167 / 100000000) (657661671 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (634733426231 / 500000000000) (634733427197 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(4763 / 5120)
  have hx13 : Bounds (-4763 / 5120) (-4763 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4763 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (357 / 5120) (357 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(4763 / 5120)
  have hx15 : Bounds (357 / 5120) (357 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(4763 / 5120)
  have hx16 : Bounds (-4763 / 5120) (-4763 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4763 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (357 / 5120) (357 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(4763 / 5120)
  have hx18 : Bounds (357 / 5120) (357 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1331586969 / 500000000) (-1331586967 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-185693964037 / 1000000000000) (-185693963757 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (43350915537 / 40000000000) (1083772890637 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (135471611053 / 250000000000) (541886445319 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (135471611053 / 250000000000) (541886445319 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-541886445319 / 1000000000000) (-135471611053 / 250000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (151260734681 / 1000000000000) (37815184197 / 250000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (151260734681 / 1000000000000) (37815184197 / 250000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (4763 / 5120)
  have hx28 : Bounds (151260734681 / 1000000000000) (37815184197 / 250000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(5949 / 6400)
  have hx30 : Bounds (12349 / 6400) (12349 / 6400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5949 / 6400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(5949 / 6400)
  have hx31 : Bounds (12349 / 6400) (12349 / 6400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5949 / 6400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (657277097 / 1000000000) (328638549 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (126823669857 / 100000000000) (1268236700501 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(5949 / 6400)
  have hx34 : Bounds (-5949 / 6400) (-5949 / 6400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5949 / 6400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (451 / 6400) (451 / 6400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(5949 / 6400)
  have hx36 : Bounds (451 / 6400) (451 / 6400) x36 := by
    exact hx35
  let x37 : ℝ := -(5949 / 6400)
  have hx37 : Bounds (-5949 / 6400) (-5949 / 6400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5949 / 6400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (451 / 6400) (451 / 6400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(5949 / 6400)
  have hx39 : Bounds (451 / 6400) (451 / 6400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-663146483 / 250000000) (-331573241 / 125000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-11682775931 / 62500000000) (-186924414613 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (540656141837 / 500000000000) (16895504467 / 15625000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (540656141837 / 1000000000000) (16895504467 / 31250000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (540656141837 / 1000000000000) (16895504467 / 31250000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-16895504467 / 31250000000) (-540656141837 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (1191336227 / 7812500000) (152491039163 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (1191336227 / 7812500000) (152491039163 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (5949 / 6400)
  have hx49 : Bounds (1191336227 / 7812500000) (152491039163 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (151260734681 / 1000000000000) (152491039163 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2203 / 2560)
  have hx52 : Bounds (4763 / 2560) (4763 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2203 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2203 / 2560)
  have hx53 : Bounds (4763 / 2560) (4763 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2203 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (620870463 / 1000000000) (9701101 / 15625000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (577579299857 / 500000000000) (46206344063 / 40000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2203 / 2560)
  have hx56 : Bounds (-2203 / 2560) (-2203 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2203 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (357 / 2560) (357 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2203 / 2560)
  have hx58 : Bounds (357 / 2560) (357 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(2203 / 2560)
  have hx59 : Bounds (-2203 / 2560) (-2203 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2203 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (357 / 2560) (357 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2203 / 2560)
  have hx61 : Bounds (357 / 2560) (357 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1970026757 / 1000000000) (-985013377 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-137363193799 / 500000000000) (-137363193589 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (220108053029 / 250000000000) (880432214397 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (220108053029 / 500000000000) (440216107199 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (220108053029 / 500000000000) (440216107199 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-440216107199 / 1000000000000) (-220108053029 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (252931072801 / 1000000000000) (126465537471 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (252931072801 / 1000000000000) (126465537471 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2203 / 2560)
  have hx71 : Bounds (252931072801 / 1000000000000) (126465537471 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2749 / 3200)
  have hx73 : Bounds (5949 / 3200) (5949 / 3200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2749 / 3200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2749 / 3200)
  have hx74 : Bounds (5949 / 3200) (5949 / 3200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2749 / 3200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (77509041 / 125000000) (620072329 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (72047075767 / 62500000000) (288188303533 / 250000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2749 / 3200)
  have hx77 : Bounds (-2749 / 3200) (-2749 / 3200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2749 / 3200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (451 / 3200) (451 / 3200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2749 / 3200)
  have hx79 : Bounds (451 / 3200) (451 / 3200) x79 := by
    exact hx78
  let x80 : ℝ := -(2749 / 3200)
  have hx80 : Bounds (-2749 / 3200) (-2749 / 3200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2749 / 3200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (451 / 3200) (451 / 3200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2749 / 3200)
  have hx82 : Bounds (451 / 3200) (451 / 3200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1959438751 / 1000000000) (-489859687 / 250000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-27615839897 / 100000000000) (-138079199273 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (438297406651 / 500000000000) (438297407793 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (438297406651 / 1000000000000) (438297407793 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (438297406651 / 1000000000000) (438297407793 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-438297407793 / 1000000000000) (-438297406651 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (254849772207 / 1000000000000) (254849774349 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (254849772207 / 1000000000000) (254849774349 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2749 / 3200)
  have hx92 : Bounds (254849772207 / 1000000000000) (254849774349 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (252931072801 / 1000000000000) (254849774349 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (316163841 / 2500000000) (5096995487 / 40000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (316163841 / 2500000000) (5096995487 / 40000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(472083 / 500000)
  have hx98 : Bounds (972083 / 500000) (972083 / 500000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472083 / 500000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(472083 / 500000)
  have hx99 : Bounds (972083 / 500000) (972083 / 500000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472083 / 500000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (664833093 / 1000000000) (332416547 / 500000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (258509179017 / 200000000000) (129254589703 / 100000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(472083 / 500000)
  have hx102 : Bounds (-472083 / 500000) (-472083 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472083 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (27917 / 500000) (27917 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(472083 / 500000)
  have hx104 : Bounds (27917 / 500000) (27917 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := -(472083 / 500000)
  have hx105 : Bounds (-472083 / 500000) (-472083 / 500000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472083 / 500000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (27917 / 500000) (27917 / 500000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(472083 / 500000)
  have hx107 : Bounds (27917 / 500000) (27917 / 500000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1442686139 / 500000000) (-2885372273 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-16110187577 / 100000000000) (-16110187549 / 100000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (226288803863 / 200000000000) (56572201077 / 50000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (565722009657 / 1000000000000) (56572201077 / 100000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (565722009657 / 1000000000000) (56572201077 / 100000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-56572201077 / 100000000000) (-565722009657 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (12742516923 / 100000000000) (127425171343 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (12742516923 / 100000000000) (127425171343 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (472083 / 500000)
  have hx117 : Bounds (12742516923 / 100000000000) (127425171343 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(472353 / 500000)
  have hx119 : Bounds (972353 / 500000) (972353 / 500000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472353 / 500000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(472353 / 500000)
  have hx120 : Bounds (972353 / 500000) (972353 / 500000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((472353 / 500000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (83138851 / 125000000) (665110809 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (646722489491 / 500000000000) (20210077827 / 15625000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(472353 / 500000)
  have hx123 : Bounds (-472353 / 500000) (-472353 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472353 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (27647 / 500000) (27647 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(472353 / 500000)
  have hx125 : Bounds (27647 / 500000) (27647 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := -(472353 / 500000)
  have hx126 : Bounds (-472353 / 500000) (-472353 / 500000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((472353 / 500000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (27647 / 500000) (27647 / 500000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(472353 / 500000)
  have hx128 : Bounds (27647 / 500000) (27647 / 500000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1447545439 / 500000000) (-2895090873 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-160081155009 / 1000000000000) (-160081154731 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1133363823973 / 1000000000000) (1133363826197 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (283340955993 / 500000000000) (566681913099 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (283340955993 / 500000000000) (566681913099 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-566681913099 / 1000000000000) (-283340955993 / 500000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (126465266901 / 1000000000000) (63232634507 / 500000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (126465266901 / 1000000000000) (63232634507 / 500000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (472353 / 500000)
  have hx138 : Bounds (126465266901 / 1000000000000) (63232634507 / 500000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (472083 / 500000) (472353 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (472353 / 500000) ≤ (63232634507 / 500000000000) := hx138.2
      have h2 : (316163841 / 2500000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (5096995487 / 40000000000) := hx96.2
      have h2 : (12742516923 / 100000000000) ≤ biasE (472083 / 500000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (214990552173 / 200000000000) (1075811060683 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (135944477507 / 1000000000000) (13708510303 / 100000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (135944477507 / 1000000000000) (13708510303 / 100000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(471557 / 500000)
  have hx143 : Bounds (971557 / 500000) (971557 / 500000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((471557 / 500000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(471557 / 500000)
  have hx144 : Bounds (971557 / 500000) (971557 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((471557 / 500000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (259489 / 390625) (664291841 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1290794774389 / 1000000000000) (1290794776333 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(471557 / 500000)
  have hx147 : Bounds (-471557 / 500000) (-471557 / 500000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((471557 / 500000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (28443 / 500000) (28443 / 500000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(471557 / 500000)
  have hx149 : Bounds (28443 / 500000) (28443 / 500000) x149 := by
    exact hx148
  let x150 : ℝ := -(471557 / 500000)
  have hx150 : Bounds (-471557 / 500000) (-471557 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((471557 / 500000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (28443 / 500000) (28443 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(471557 / 500000)
  have hx152 : Bounds (28443 / 500000) (28443 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-89584563 / 31250000) (-2866706011 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-163075438427 / 1000000000000) (-163075438141 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (563859667981 / 500000000000) (70482458637 / 62500000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (563859667981 / 1000000000000) (70482458637 / 125000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (563859667981 / 1000000000000) (70482458637 / 125000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-70482458637 / 125000000000) (-563859667981 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (16160938863 / 125000000000) (129287513019 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (16160938863 / 125000000000) (129287513019 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (471557 / 500000)
  have hx162 : Bounds (16160938863 / 125000000000) (129287513019 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(2949 / 3125)
  have hx164 : Bounds (6074 / 3125) (6074 / 3125) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2949 / 3125) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(2949 / 3125)
  have hx165 : Bounds (6074 / 3125) (6074 / 3125) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2949 / 3125) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (664583083 / 1000000000) (166145771 / 250000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (258347369353 / 200000000000) (129173684871 / 100000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(2949 / 3125)
  have hx168 : Bounds (-2949 / 3125) (-2949 / 3125) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2949 / 3125) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (176 / 3125) (176 / 3125) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(2949 / 3125)
  have hx170 : Bounds (176 / 3125) (176 / 3125) x170 := by
    exact hx169
  let x171 : ℝ := -(2949 / 3125)
  have hx171 : Bounds (-2949 / 3125) (-2949 / 3125) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2949 / 3125) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (176 / 3125) (176 / 3125) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(2949 / 3125)
  have hx173 : Bounds (176 / 3125) (176 / 3125) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-2876705569 / 1000000000) (-719176391 / 250000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-162016057647 / 1000000000000) (-40504014341 / 250000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (564860394559 / 500000000000) (564860395673 / 500000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (564860394559 / 1000000000000) (564860395673 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (564860394559 / 1000000000000) (564860395673 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-564860395673 / 1000000000000) (-564860394559 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (128286784327 / 1000000000000) (128286786441 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (128286784327 / 1000000000000) (128286786441 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (2949 / 3125)
  have hx183 : Bounds (128286784327 / 1000000000000) (128286786441 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(471557 / 500000)
  have hx184 : Bounds (128211139959 / 1000000000000) (6464343993 / 50000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((471557 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(2949 / 3125)
  have hx185 : Bounds (128288084533 / 1000000000000) (32341117507 / 250000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((2949 / 3125) : ℝ)) <;> norm_num
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
  have hc : Bounds (471557 / 500000) (2949 / 3125) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (471557 / 500000) ≤ (6464343993 / 50000000000) := hx184.2
      have h2 : (16160938863 / 125000000000) ≤ biasE (471557 / 500000) := hx162.1
      linarith
    · have h1 : biasE (2949 / 3125) ≤ (128286786441 / 1000000000000) := hx183.2
      have h2 : (128288084533 / 1000000000000) ≤ x141 * (2949 / 3125) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (972083 / 500000) (972353 / 500000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-472353 / 500000) (-472083 / 500000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (27647 / 500000) (27917 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (27647 / 500000) (27917 / 500000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (8955116953827 / 500000000000) (18085144862011 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (8705116953827 / 250000000000) (17585144862011 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (8705116953827 / 250000000000) (17585144862011 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1775102683 / 500000000) (3560201687 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1775102683 / 1000000000) (3560201687 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1775102683 / 1000000000) (3560201687 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (971557 / 500000) (6074 / 3125) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-2949 / 3125) (-471557 / 500000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (176 / 3125) (28443 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (176 / 3125) (28443 / 500000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (17579017684491 / 1000000000000) (8877840909091 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (17079017684491 / 500000000000) (8627840909091 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (17079017684491 / 500000000000) (8627840909091 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (3530997851 / 1000000000) (3541288653 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (3530997851 / 2000000000) (3541288653 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (3530997851 / 2000000000) (3541288653 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (151260734681 / 500000000000) (152491039163 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (316163841 / 1250000000) (5096995487 / 20000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-5096995487 / 20000000000) (-316163841 / 1250000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (11917923753 / 250000000000) (26025502763 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (11917923753 / 250000000000) (26025502763 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1675991599797 / 1000000000000) (84083597373 / 50000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-84083597373 / 50000000000) (-1675991599797 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-51062507889 / 31250000000) (-1623940594271 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-51062507889 / 31250000000) (-1623940594271 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1641086423093 / 1000000000000) (411795846051 / 250000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1417234129 / 200000000000) (23242789933 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (357 / 10240) (451 / 12800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (357 / 10240) ≤ m → m ≤ (451 / 12800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142

end


