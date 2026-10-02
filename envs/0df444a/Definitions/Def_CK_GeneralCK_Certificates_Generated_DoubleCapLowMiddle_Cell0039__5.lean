-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0039__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0039__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:36:35.303475+00:00
-- url     : https://prove2.me/theorems/26d95a36-a096-492a-998d-241d5d1e1653
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0039 (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0040, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0041, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0042, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0043).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0036Logs__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0040Logs__5

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (83 / 6400) (107 / 8192) m) :
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
  have hx0 : Bounds (83 / 3200) (107 / 4096) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-107 / 4096) (-83 / 3200) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (3989 / 4096) (3117 / 3200) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (3989 / 4096) (3117 / 3200) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (83 / 1600) (107 / 2048) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-107 / 2048) (-83 / 1600) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1941 / 2048) (1517 / 1600) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (1941 / 2048) (1517 / 1600) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(3117 / 3200)
  have hx9 : Bounds (6317 / 3200) (6317 / 3200) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3117 / 3200) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(3117 / 3200)
  have hx10 : Bounds (6317 / 3200) (6317 / 3200) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3117 / 3200) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (340046801 / 500000000) (680093603 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (671273638099 / 500000000000) (1342547278173 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(3117 / 3200)
  have hx13 : Bounds (-3117 / 3200) (-3117 / 3200) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3117 / 3200) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (83 / 3200) (83 / 3200) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(3117 / 3200)
  have hx15 : Bounds (83 / 3200) (83 / 3200) x15 := by
    exact hx14
  let x16 : ℝ := -(3117 / 3200)
  have hx16 : Bounds (-3117 / 3200) (-3117 / 3200) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3117 / 3200) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (83 / 3200) (83 / 3200) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(3117 / 3200)
  have hx18 : Bounds (83 / 3200) (83 / 3200) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-913016371 / 250000000) (-1826032739 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-23681362123 / 250000000000) (-18945089667 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (623910913853 / 500000000000) (623910914919 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (623910913853 / 1000000000000) (623910914919 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (623910913853 / 1000000000000) (623910914919 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-623910914919 / 1000000000000) (-623910913853 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (69236265081 / 1000000000000) (69236267147 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (69236265081 / 1000000000000) (69236267147 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (3117 / 3200)
  have hx28 : Bounds (69236265081 / 1000000000000) (69236267147 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(3989 / 4096)
  have hx30 : Bounds (8085 / 4096) (8085 / 4096) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3989 / 4096) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(3989 / 4096)
  have hx31 : Bounds (8085 / 4096) (8085 / 4096) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3989 / 4096) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (135999921 / 200000000) (339999803 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (1342235548443 / 1000000000000) (671117775209 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(3989 / 4096)
  have hx34 : Bounds (-3989 / 4096) (-3989 / 4096) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3989 / 4096) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (107 / 4096) (107 / 4096) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(3989 / 4096)
  have hx36 : Bounds (107 / 4096) (107 / 4096) x36 := by
    exact hx35
  let x37 : ℝ := -(3989 / 4096)
  have hx37 : Bounds (-3989 / 4096) (-3989 / 4096) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3989 / 4096) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (107 / 4096) (107 / 4096) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(3989 / 4096)
  have hx39 : Bounds (107 / 4096) (107 / 4096) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-728987467 / 200000000) (-3644937329 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-95216868859 / 1000000000000) (-95216868701 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (38969333737 / 31250000000) (1247018681717 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (38969333737 / 62500000000) (623509340859 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (38969333737 / 62500000000) (623509340859 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-623509340859 / 1000000000000) (-38969333737 / 62500000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (69637839141 / 1000000000000) (8704730151 / 125000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (69637839141 / 1000000000000) (8704730151 / 125000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (3989 / 4096)
  have hx49 : Bounds (69637839141 / 1000000000000) (8704730151 / 125000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (69236265081 / 1000000000000) (8704730151 / 125000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1517 / 1600)
  have hx52 : Bounds (3117 / 1600) (3117 / 1600) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1517 / 1600) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1517 / 1600)
  have hx53 : Bounds (3117 / 1600) (3117 / 1600) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1517 / 1600) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (666867371 / 1000000000) (166716843 / 250000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1299140997129 / 1000000000000) (649570499539 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1517 / 1600)
  have hx56 : Bounds (-1517 / 1600) (-1517 / 1600) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1517 / 1600) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (83 / 1600) (83 / 1600) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1517 / 1600)
  have hx58 : Bounds (83 / 1600) (83 / 1600) x58 := by
    exact hx57
  let x59 : ℝ := -(1517 / 1600)
  have hx59 : Bounds (-1517 / 1600) (-1517 / 1600) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1517 / 1600) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (83 / 1600) (83 / 1600) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1517 / 1600)
  have hx61 : Bounds (83 / 1600) (83 / 1600) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2958918303 / 1000000000) (-1479459149 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-153493886969 / 1000000000000) (-38373471677 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (14320588877 / 12500000000) (114564711237 / 100000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (14320588877 / 25000000000) (114564711237 / 200000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (14320588877 / 25000000000) (114564711237 / 200000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-114564711237 / 200000000000) (-14320588877 / 25000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (24064724763 / 200000000000) (376011331 / 3125000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (24064724763 / 200000000000) (376011331 / 3125000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1517 / 1600)
  have hx71 : Bounds (24064724763 / 200000000000) (376011331 / 3125000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1941 / 2048)
  have hx73 : Bounds (3989 / 2048) (3989 / 2048) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 2048) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1941 / 2048)
  have hx74 : Bounds (3989 / 2048) (3989 / 2048) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 2048) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (133335373 / 200000000) (333338433 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (129852246801 / 100000000000) (1298522469959 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1941 / 2048)
  have hx77 : Bounds (-1941 / 2048) (-1941 / 2048) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 2048) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (107 / 2048) (107 / 2048) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1941 / 2048)
  have hx79 : Bounds (107 / 2048) (107 / 2048) x79 := by
    exact hx78
  let x80 : ℝ := -(1941 / 2048)
  have hx80 : Bounds (-1941 / 2048) (-1941 / 2048) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 2048) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (107 / 2048) (107 / 2048) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1941 / 2048)
  have hx82 : Bounds (107 / 2048) (107 / 2048) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1475895077 / 500000000) (-2951790149 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-154219505117 / 1000000000000) (-77109752427 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (1144302962893 / 1000000000000) (228860593021 / 200000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (286075740723 / 500000000000) (572151482553 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (286075740723 / 500000000000) (572151482553 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-572151482553 / 1000000000000) (-286075740723 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (120995697447 / 1000000000000) (60497849777 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (120995697447 / 1000000000000) (60497849777 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1941 / 2048)
  have hx92 : Bounds (120995697447 / 1000000000000) (60497849777 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (24064724763 / 200000000000) (60497849777 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (60161811907 / 1000000000000) (60497849777 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (60161811907 / 1000000000000) (60497849777 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(489011 / 500000)
  have hx98 : Bounds (989011 / 500000) (989011 / 500000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489011 / 500000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(489011 / 500000)
  have hx99 : Bounds (989011 / 500000) (989011 / 500000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489011 / 500000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (136419471 / 200000000) (170524339 / 250000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1349203574331 / 1000000000000) (134920357631 / 100000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(489011 / 500000)
  have hx102 : Bounds (-489011 / 500000) (-489011 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489011 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (10989 / 500000) (10989 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(489011 / 500000)
  have hx104 : Bounds (10989 / 500000) (10989 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := -(489011 / 500000)
  have hx105 : Bounds (-489011 / 500000) (-489011 / 500000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489011 / 500000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (10989 / 500000) (10989 / 500000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(489011 / 500000)
  have hx107 : Bounds (10989 / 500000) (10989 / 500000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-3817713329 / 1000000000) (-3817713323 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-16781140709 / 200000000000) (-20976425853 / 250000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (632648935393 / 500000000000) (632648936449 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (632648935393 / 1000000000000) (632648936449 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (632648935393 / 1000000000000) (632648936449 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-632648936449 / 1000000000000) (-632648935393 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (60498243551 / 1000000000000) (60498245607 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (60498243551 / 1000000000000) (60498245607 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (489011 / 500000)
  have hx117 : Bounds (60498243551 / 1000000000000) (60498245607 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(244543 / 250000)
  have hx119 : Bounds (494543 / 250000) (494543 / 250000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244543 / 250000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(244543 / 250000)
  have hx120 : Bounds (494543 / 250000) (494543 / 250000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244543 / 250000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (136434637 / 200000000) (341086593 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1349455893717 / 1000000000000) (84340993481 / 62500000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(244543 / 250000)
  have hx123 : Bounds (-244543 / 250000) (-244543 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244543 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (5457 / 250000) (5457 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(244543 / 250000)
  have hx125 : Bounds (5457 / 250000) (5457 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := -(244543 / 250000)
  have hx126 : Bounds (-244543 / 250000) (-244543 / 250000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244543 / 250000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (5457 / 250000) (5457 / 250000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(244543 / 250000)
  have hx128 : Bounds (5457 / 250000) (5457 / 250000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-956140433 / 250000000) (-1912280863 / 500000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-83482533487 / 1000000000000) (-16696506671 / 200000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (126597336023 / 100000000000) (1265973362341 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (126597336023 / 200000000000) (632986681171 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (126597336023 / 200000000000) (632986681171 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-632986681171 / 1000000000000) (-126597336023 / 200000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (60160498829 / 1000000000000) (12032100177 / 200000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (60160498829 / 1000000000000) (12032100177 / 200000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (244543 / 250000)
  have hx138 : Bounds (60160498829 / 1000000000000) (12032100177 / 200000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (489011 / 500000) (244543 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (244543 / 250000) ≤ (12032100177 / 200000000000) := hx138.2
      have h2 : (60161811907 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (60497849777 / 1000000000000) := hx96.2
      have h2 : (60498243551 / 1000000000000) ≤ biasE (489011 / 500000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (102662816811 / 100000000000) (205364753071 / 200000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (15440952687 / 250000000000) (3882539369 / 62500000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (15440952687 / 250000000000) (3882539369 / 62500000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(97791 / 100000)
  have hx143 : Bounds (197791 / 100000) (197791 / 100000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97791 / 100000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(97791 / 100000)
  have hx144 : Bounds (197791 / 100000) (197791 / 100000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97791 / 100000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (682040731 / 1000000000) (170510183 / 250000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (337253795563 / 250000000000) (1349015184231 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(97791 / 100000)
  have hx147 : Bounds (-97791 / 100000) (-97791 / 100000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97791 / 100000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (2209 / 100000) (2209 / 100000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(97791 / 100000)
  have hx149 : Bounds (2209 / 100000) (2209 / 100000) x149 := by
    exact hx148
  let x150 : ℝ := -(97791 / 100000)
  have hx150 : Bounds (-97791 / 100000) (-97791 / 100000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97791 / 100000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (2209 / 100000) (2209 / 100000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(97791 / 100000)
  have hx152 : Bounds (2209 / 100000) (2209 / 100000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-476578783 / 125000000) (-1906315129 / 500000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-21055250633 / 250000000000) (-84221002399 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (31619854493 / 25000000000) (158099272729 / 125000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (31619854493 / 50000000000) (158099272729 / 250000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (31619854493 / 50000000000) (158099272729 / 250000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-158099272729 / 250000000000) (-31619854493 / 50000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (15187522271 / 250000000000) (3037504557 / 50000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (15187522271 / 250000000000) (3037504557 / 50000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (97791 / 100000)
  have hx162 : Bounds (15187522271 / 250000000000) (3037504557 / 50000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(489031 / 500000)
  have hx164 : Bounds (989031 / 500000) (989031 / 500000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489031 / 500000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(489031 / 500000)
  have hx165 : Bounds (989031 / 500000) (989031 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((489031 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (682117577 / 1000000000) (341058789 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (269854171719 / 200000000000) (674635430287 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(489031 / 500000)
  have hx168 : Bounds (-489031 / 500000) (-489031 / 500000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489031 / 500000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (10969 / 500000) (10969 / 500000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(489031 / 500000)
  have hx170 : Bounds (10969 / 500000) (10969 / 500000) x170 := by
    exact hx169
  let x171 : ℝ := -(489031 / 500000)
  have hx171 : Bounds (-489031 / 500000) (-489031 / 500000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((489031 / 500000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (10969 / 500000) (10969 / 500000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(489031 / 500000)
  have hx173 : Bounds (10969 / 500000) (10969 / 500000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-3819534989 / 1000000000) (-3819534983 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-83792958589 / 1000000000000) (-83792958457 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (632738950003 / 500000000000) (1265477902117 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (632738950003 / 1000000000000) (632738951059 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (632738950003 / 1000000000000) (632738951059 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-632738951059 / 1000000000000) (-632738950003 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (60408228941 / 1000000000000) (60408230997 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (60408228941 / 1000000000000) (60408230997 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (489031 / 500000)
  have hx183 : Bounds (60408228941 / 1000000000000) (60408230997 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(97791 / 100000)
  have hx184 : Bounds (7549931021 / 125000000000) (6074838519 / 100000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((97791 / 100000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(489031 / 500000)
  have hx185 : Bounds (60408836267 / 1000000000000) (30378913763 / 500000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((489031 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (97791 / 100000) (489031 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (97791 / 100000) ≤ (6074838519 / 100000000000) := hx184.2
      have h2 : (15187522271 / 250000000000) ≤ biasE (97791 / 100000) := hx162.1
      linarith
    · have h1 : biasE (489031 / 500000) ≤ (60408230997 / 1000000000000) := hx183.2
      have h2 : (60408836267 / 1000000000000) ≤ x141 * (489031 / 500000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (989011 / 500000) (494543 / 250000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-244543 / 250000) (-489011 / 500000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (5457 / 250000) (10989 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (5457 / 250000) (10989 / 500000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (9100009100009 / 200000000000) (45812717610409 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (9000009100009 / 100000000000) (45312717610409 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (9000009100009 / 100000000000) (45312717610409 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (2249905339 / 500000000) (4506734919 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (2249905339 / 1000000000) (4506734919 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (2249905339 / 1000000000) (4506734919 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (197791 / 100000) (989031 / 500000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-489031 / 500000) (-97791 / 100000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (10969 / 500000) (2209 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (10969 / 500000) (2209 / 100000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (45269352648257 / 1000000000000) (45583006655119 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (44769352648257 / 500000000000) (45083006655119 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (44769352648257 / 500000000000) (45083006655119 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (4494670989 / 1000000000) (4501652567 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (4494670989 / 2000000000) (4501652567 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (4494670989 / 2000000000) (4501652567 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (69236265081 / 500000000000) (8704730151 / 62500000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (60161811907 / 500000000000) (60497849777 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-60497849777 / 500000000000) (-60161811907 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (1092301913 / 62500000000) (9476029301 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (1092301913 / 62500000000) (9476029301 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2200456919459 / 1000000000000) (440836190919 / 200000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-440836190919 / 200000000000) (-2200456919459 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2186704123987 / 1000000000000) (-2181504860857 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2186704123987 / 1000000000000) (-2181504860857 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2188628244033 / 1000000000000) (548111369193 / 250000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (962060023 / 500000000000) (2188123183 / 200000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (83 / 6400) (107 / 8192) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (83 / 6400) ≤ m → m ≤ (107 / 8192) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (107 / 8192) (1347 / 102400) m) :
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
  have hx0 : Bounds (107 / 4096) (1347 / 51200) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1347 / 51200) (-107 / 4096) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (49853 / 51200) (3989 / 4096) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (49853 / 51200) (3989 / 4096) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (107 / 2048) (1347 / 25600) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1347 / 25600) (-107 / 2048) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (24253 / 25600) (1941 / 2048) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (24253 / 25600) (1941 / 2048) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(3989 / 4096)
  have hx9 : Bounds (8085 / 4096) (8085 / 4096) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3989 / 4096) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(3989 / 4096)
  have hx10 : Bounds (8085 / 4096) (8085 / 4096) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3989 / 4096) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (135999921 / 200000000) (339999803 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (1342235548443 / 1000000000000) (671117775209 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(3989 / 4096)
  have hx13 : Bounds (-3989 / 4096) (-3989 / 4096) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3989 / 4096) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (107 / 4096) (107 / 4096) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(3989 / 4096)
  have hx15 : Bounds (107 / 4096) (107 / 4096) x15 := by
    exact hx14
  let x16 : ℝ := -(3989 / 4096)
  have hx16 : Bounds (-3989 / 4096) (-3989 / 4096) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3989 / 4096) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (107 / 4096) (107 / 4096) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(3989 / 4096)
  have hx18 : Bounds (107 / 4096) (107 / 4096) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-728987467 / 200000000) (-3644937329 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-95216868859 / 1000000000000) (-95216868701 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (38969333737 / 31250000000) (1247018681717 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (38969333737 / 62500000000) (623509340859 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (38969333737 / 62500000000) (623509340859 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-623509340859 / 1000000000000) (-38969333737 / 62500000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (69637839141 / 1000000000000) (8704730151 / 125000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (69637839141 / 1000000000000) (8704730151 / 125000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (3989 / 4096)
  have hx28 : Bounds (69637839141 / 1000000000000) (8704730151 / 125000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(49853 / 51200)
  have hx30 : Bounds (101053 / 51200) (101053 / 51200) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49853 / 51200) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(49853 / 51200)
  have hx31 : Bounds (101053 / 51200) (101053 / 51200) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49853 / 51200) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (679905599 / 1000000000) (424941 / 625000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (1341923837807 / 1000000000000) (670961919891 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(49853 / 51200)
  have hx34 : Bounds (-49853 / 51200) (-49853 / 51200) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49853 / 51200) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1347 / 51200) (1347 / 51200) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(49853 / 51200)
  have hx36 : Bounds (1347 / 51200) (1347 / 51200) x36 := by
    exact hx35
  let x37 : ℝ := -(49853 / 51200)
  have hx37 : Bounds (-49853 / 51200) (-49853 / 51200) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49853 / 51200) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1347 / 51200) (1347 / 51200) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(49853 / 51200)
  have hx39 : Bounds (1347 / 51200) (1347 / 51200) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-3637859637 / 1000000000) (-3637859631 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-9570697131 / 100000000000) (-95706971151 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1246216866497 / 1000000000000) (1246216868631 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (19472138539 / 31250000000) (155777108579 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (19472138539 / 31250000000) (155777108579 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-155777108579 / 250000000000) (-19472138539 / 31250000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (17509686421 / 250000000000) (8754843469 / 125000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (17509686421 / 250000000000) (8754843469 / 125000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (49853 / 51200)
  have hx49 : Bounds (17509686421 / 250000000000) (8754843469 / 125000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (69637839141 / 1000000000000) (8754843469 / 125000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1941 / 2048)
  have hx52 : Bounds (3989 / 2048) (3989 / 2048) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 2048) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1941 / 2048)
  have hx53 : Bounds (3989 / 2048) (3989 / 2048) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 2048) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (133335373 / 200000000) (333338433 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (129852246801 / 100000000000) (1298522469959 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1941 / 2048)
  have hx56 : Bounds (-1941 / 2048) (-1941 / 2048) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 2048) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (107 / 2048) (107 / 2048) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1941 / 2048)
  have hx58 : Bounds (107 / 2048) (107 / 2048) x58 := by
    exact hx57
  let x59 : ℝ := -(1941 / 2048)
  have hx59 : Bounds (-1941 / 2048) (-1941 / 2048) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 2048) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (107 / 2048) (107 / 2048) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1941 / 2048)
  have hx61 : Bounds (107 / 2048) (107 / 2048) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1475895077 / 500000000) (-2951790149 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-154219505117 / 1000000000000) (-77109752427 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1144302962893 / 1000000000000) (228860593021 / 200000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (286075740723 / 500000000000) (572151482553 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (286075740723 / 500000000000) (572151482553 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-572151482553 / 1000000000000) (-286075740723 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (120995697447 / 1000000000000) (60497849777 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (120995697447 / 1000000000000) (60497849777 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1941 / 2048)
  have hx71 : Bounds (120995697447 / 1000000000000) (60497849777 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(24253 / 25600)
  have hx73 : Bounds (49853 / 25600) (49853 / 25600) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24253 / 25600) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(24253 / 25600)
  have hx74 : Bounds (49853 / 25600) (49853 / 25600) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24253 / 25600) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (666486323 / 1000000000) (166621581 / 250000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (20279750159 / 15625000000) (324476003031 / 250000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(24253 / 25600)
  have hx77 : Bounds (-24253 / 25600) (-24253 / 25600) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24253 / 25600) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1347 / 25600) (1347 / 25600) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(24253 / 25600)
  have hx79 : Bounds (1347 / 25600) (1347 / 25600) x79 := by
    exact hx78
  let x80 : ℝ := -(24253 / 25600)
  have hx80 : Bounds (-24253 / 25600) (-24253 / 25600) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24253 / 25600) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1347 / 25600) (1347 / 25600) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(24253 / 25600)
  have hx82 : Bounds (1347 / 25600) (1347 / 25600) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-368089057 / 125000000) (-2944712451 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-154942487431 / 1000000000000) (-154942487167 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (228592304549 / 200000000000) (1142961524957 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (142870190343 / 250000000000) (571480762479 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (142870190343 / 250000000000) (571480762479 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-571480762479 / 1000000000000) (-142870190343 / 250000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (121666417521 / 1000000000000) (30416604907 / 250000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (121666417521 / 1000000000000) (30416604907 / 250000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (24253 / 25600)
  have hx92 : Bounds (121666417521 / 1000000000000) (30416604907 / 250000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (120995697447 / 1000000000000) (30416604907 / 250000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (60497848723 / 1000000000000) (30416604907 / 500000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (60497848723 / 1000000000000) (30416604907 / 500000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(977873 / 1000000)
  have hx98 : Bounds (1977873 / 1000000) (1977873 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977873 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(977873 / 1000000)
  have hx99 : Bounds (1977873 / 1000000) (1977873 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977873 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (85252753 / 125000000) (27280881 / 40000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (674476473337 / 500000000000) (1348952948653 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(977873 / 1000000)
  have hx102 : Bounds (-977873 / 1000000) (-977873 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977873 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (22127 / 1000000) (22127 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(977873 / 1000000)
  have hx104 : Bounds (22127 / 1000000) (22127 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(977873 / 1000000)
  have hx105 : Bounds (-977873 / 1000000) (-977873 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977873 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (22127 / 1000000) (22127 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(977873 / 1000000)
  have hx107 : Bounds (22127 / 1000000) (22127 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-3810956699 / 1000000000) (-3810956693 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-84325038879 / 1000000000000) (-42162519373 / 500000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (252925581559 / 200000000000) (1264627909907 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (632313953897 / 1000000000000) (316156977477 / 500000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (632313953897 / 1000000000000) (316156977477 / 500000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-316156977477 / 500000000000) (-632313953897 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (30416612523 / 500000000000) (60833227103 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (30416612523 / 500000000000) (60833227103 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (977873 / 1000000)
  have hx117 : Bounds (30416612523 / 500000000000) (60833227103 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(978023 / 1000000)
  have hx119 : Bounds (1978023 / 1000000) (1978023 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978023 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(978023 / 1000000)
  have hx120 : Bounds (1978023 / 1000000) (1978023 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((978023 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (682097861 / 1000000000) (341048931 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (337301314327 / 250000000000) (1349205259287 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(978023 / 1000000)
  have hx123 : Bounds (-978023 / 1000000) (-978023 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978023 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (21977 / 1000000) (21977 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(978023 / 1000000)
  have hx125 : Bounds (21977 / 1000000) (21977 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(978023 / 1000000)
  have hx126 : Bounds (-978023 / 1000000) (-978023 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((978023 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (21977 / 1000000) (21977 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(978023 / 1000000)
  have hx128 : Bounds (21977 / 1000000) (21977 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-381775883 / 100000000) (-477219853 / 125000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-83902885807 / 1000000000000) (-3356115427 / 40000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1265302371501 / 1000000000000) (316325593403 / 250000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (2530604743 / 4000000000) (316325593403 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (2530604743 / 4000000000) (316325593403 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-316325593403 / 500000000000) (-2530604743 / 4000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (30247996597 / 500000000000) (241983981 / 4000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (30247996597 / 500000000000) (241983981 / 4000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (978023 / 1000000)
  have hx138 : Bounds (30247996597 / 500000000000) (241983981 / 4000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (977873 / 1000000) (978023 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (978023 / 1000000) ≤ (241983981 / 4000000000) := hx138.2
      have h2 : (60497848723 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (30416604907 / 500000000000) := hx96.2
      have h2 : (30416612523 / 500000000000) ≤ biasE (977873 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (513411882677 / 500000000000) (513509718573 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (62120628821 / 1000000000000) (62476888903 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (62120628821 / 1000000000000) (62476888903 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(977759 / 1000000)
  have hx143 : Bounds (1977759 / 1000000) (1977759 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977759 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(977759 / 1000000)
  have hx144 : Bounds (1977759 / 1000000) (1977759 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977759 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (136392877 / 200000000) (340982193 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1348761200113 / 1000000000000) (1348761202091 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(977759 / 1000000)
  have hx147 : Bounds (-977759 / 1000000) (-977759 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977759 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (22241 / 1000000) (22241 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(977759 / 1000000)
  have hx149 : Bounds (22241 / 1000000) (22241 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(977759 / 1000000)
  have hx150 : Bounds (-977759 / 1000000) (-977759 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977759 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (22241 / 1000000) (22241 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(977759 / 1000000)
  have hx152 : Bounds (22241 / 1000000) (22241 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3805817849 / 1000000000) (-3805817843 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-4232259739 / 50000000000) (-42322597323 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1264116005333 / 1000000000000) (252823201489 / 200000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (316029001333 / 500000000000) (632058003723 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (316029001333 / 500000000000) (632058003723 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-632058003723 / 1000000000000) (-316029001333 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (61089176277 / 1000000000000) (30544589167 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (61089176277 / 1000000000000) (30544589167 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (977759 / 1000000)
  have hx162 : Bounds (61089176277 / 1000000000000) (30544589167 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(977911 / 1000000)
  have hx164 : Bounds (1977911 / 1000000) (1977911 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977911 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(977911 / 1000000)
  have hx165 : Bounds (1977911 / 1000000) (1977911 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977911 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (682041237 / 1000000000) (341020619 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (269803373023 / 200000000000) (674508433547 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(977911 / 1000000)
  have hx168 : Bounds (-977911 / 1000000) (-977911 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977911 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (22089 / 1000000) (22089 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(977911 / 1000000)
  have hx170 : Bounds (22089 / 1000000) (22089 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(977911 / 1000000)
  have hx171 : Bounds (-977911 / 1000000) (-977911 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977911 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (22089 / 1000000) (22089 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(977911 / 1000000)
  have hx173 : Bounds (22089 / 1000000) (22089 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-762535107 / 200000000) (-3812675529 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-84218189893 / 1000000000000) (-263181843 / 3125000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (632399337611 / 500000000000) (632399338667 / 500000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (632399337611 / 1000000000000) (632399338667 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (632399337611 / 1000000000000) (632399338667 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-632399338667 / 1000000000000) (-632399337611 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (60747841333 / 1000000000000) (60747843389 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (60747841333 / 1000000000000) (60747843389 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (977911 / 1000000)
  have hx183 : Bounds (60747841333 / 1000000000000) (60747843389 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(977759 / 1000000)
  have hx184 : Bounds (12147800783 / 200000000000) (61087340417 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((977759 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(977911 / 1000000)
  have hx185 : Bounds (48598757 / 800000000) (12219367381 / 200000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((977911 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (977759 / 1000000) (977911 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (977759 / 1000000) ≤ (61087340417 / 1000000000000) := hx184.2
      have h2 : (61089176277 / 1000000000000) ≤ biasE (977759 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (977911 / 1000000) ≤ (60747843389 / 1000000000000) := hx183.2
      have h2 : (48598757 / 800000000) ≤ x141 * (977911 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1977873 / 1000000) (1978023 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-978023 / 1000000) (-977873 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (21977 / 1000000) (22127 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (21977 / 1000000) (22127 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (2824603425679 / 62500000000) (45502115848387 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (2793353425679 / 31250000000) (45002115848387 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (2793353425679 / 31250000000) (45002115848387 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (2246489359 / 500000000) (4499856691 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (2246489359 / 1000000000) (4499856691 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (2246489359 / 1000000000) (4499856691 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1977759 / 1000000) (1977911 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-977911 / 1000000) (-977759 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (22089 / 1000000) (22241 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (22089 / 1000000) (22241 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (44962007103997 / 1000000000000) (22635701027661 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (44462007103997 / 500000000000) (22385701027661 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (44462007103997 / 500000000000) (22385701027661 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (1121945557 / 250000000) (1123679193 / 250000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (1121945557 / 500000000) (1123679193 / 500000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (1121945557 / 500000000) (1123679193 / 500000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (69637839141 / 500000000000) (8754843469 / 62500000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (60497848723 / 500000000000) (30416604907 / 250000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-30416604907 / 250000000000) (-60497848723 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (8804629327 / 500000000000) (9540899029 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (8804629327 / 500000000000) (9540899029 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2196781288953 / 1000000000000) (2200481670251 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2200481670251 / 1000000000000) (-2196781288953 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2182872411597 / 1000000000000) (-435539898179 / 200000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2182872411597 / 1000000000000) (-435539898179 / 200000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1092428747131 / 500000000000) (1094325268769 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (397016533 / 200000000000) (10951046643 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (107 / 8192) (1347 / 102400) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (107 / 8192) ≤ m → m ≤ (1347 / 102400) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1347 / 102400) (2713 / 204800) m) :
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
  have hx0 : Bounds (1347 / 51200) (2713 / 102400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-2713 / 102400) (-1347 / 51200) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (99687 / 102400) (49853 / 51200) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (99687 / 102400) (49853 / 51200) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1347 / 25600) (2713 / 51200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-2713 / 51200) (-1347 / 25600) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (48487 / 51200) (24253 / 25600) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (48487 / 51200) (24253 / 25600) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(49853 / 51200)
  have hx9 : Bounds (101053 / 51200) (101053 / 51200) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49853 / 51200) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(49853 / 51200)
  have hx10 : Bounds (101053 / 51200) (101053 / 51200) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49853 / 51200) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (679905599 / 1000000000) (424941 / 625000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (1341923837807 / 1000000000000) (670961919891 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(49853 / 51200)
  have hx13 : Bounds (-49853 / 51200) (-49853 / 51200) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49853 / 51200) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1347 / 51200) (1347 / 51200) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(49853 / 51200)
  have hx15 : Bounds (1347 / 51200) (1347 / 51200) x15 := by
    exact hx14
  let x16 : ℝ := -(49853 / 51200)
  have hx16 : Bounds (-49853 / 51200) (-49853 / 51200) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49853 / 51200) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1347 / 51200) (1347 / 51200) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(49853 / 51200)
  have hx18 : Bounds (1347 / 51200) (1347 / 51200) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-3637859637 / 1000000000) (-3637859631 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-9570697131 / 100000000000) (-95706971151 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1246216866497 / 1000000000000) (1246216868631 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (19472138539 / 31250000000) (155777108579 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (19472138539 / 31250000000) (155777108579 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-155777108579 / 250000000000) (-19472138539 / 31250000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (17509686421 / 250000000000) (8754843469 / 125000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (17509686421 / 250000000000) (8754843469 / 125000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (49853 / 51200)
  have hx28 : Bounds (17509686421 / 250000000000) (8754843469 / 125000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(99687 / 102400)
  have hx30 : Bounds (202087 / 102400) (202087 / 102400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99687 / 102400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(99687 / 102400)
  have hx31 : Bounds (202087 / 102400) (202087 / 102400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99687 / 102400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (135962317 / 200000000) (339905793 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (335403036567 / 250000000000) (1341612148243 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(99687 / 102400)
  have hx34 : Bounds (-99687 / 102400) (-99687 / 102400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99687 / 102400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (2713 / 102400) (2713 / 102400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(99687 / 102400)
  have hx36 : Bounds (2713 / 102400) (2713 / 102400) x36 := by
    exact hx35
  let x37 : ℝ := -(99687 / 102400)
  have hx37 : Bounds (-99687 / 102400) (-99687 / 102400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99687 / 102400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (2713 / 102400) (2713 / 102400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(99687 / 102400)
  have hx39 : Bounds (2713 / 102400) (2713 / 102400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1815415841 / 500000000) (-907707919 / 250000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-96195765169 / 1000000000000) (-96195765009 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1245416381099 / 1000000000000) (622708191617 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (622708190549 / 1000000000000) (622708191617 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (622708190549 / 1000000000000) (622708191617 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-622708191617 / 1000000000000) (-622708190549 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (70438988383 / 1000000000000) (70438990451 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (70438988383 / 1000000000000) (70438990451 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (99687 / 102400)
  have hx49 : Bounds (70438988383 / 1000000000000) (70438990451 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (17509686421 / 250000000000) (70438990451 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(24253 / 25600)
  have hx52 : Bounds (49853 / 25600) (49853 / 25600) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24253 / 25600) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(24253 / 25600)
  have hx53 : Bounds (49853 / 25600) (49853 / 25600) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24253 / 25600) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (666486323 / 1000000000) (166621581 / 250000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (20279750159 / 15625000000) (324476003031 / 250000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(24253 / 25600)
  have hx56 : Bounds (-24253 / 25600) (-24253 / 25600) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24253 / 25600) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1347 / 25600) (1347 / 25600) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(24253 / 25600)
  have hx58 : Bounds (1347 / 25600) (1347 / 25600) x58 := by
    exact hx57
  let x59 : ℝ := -(24253 / 25600)
  have hx59 : Bounds (-24253 / 25600) (-24253 / 25600) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24253 / 25600) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1347 / 25600) (1347 / 25600) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(24253 / 25600)
  have hx61 : Bounds (1347 / 25600) (1347 / 25600) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-368089057 / 125000000) (-2944712451 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-154942487431 / 1000000000000) (-154942487167 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (228592304549 / 200000000000) (1142961524957 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (142870190343 / 250000000000) (571480762479 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (142870190343 / 250000000000) (571480762479 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-571480762479 / 1000000000000) (-142870190343 / 250000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (121666417521 / 1000000000000) (30416604907 / 250000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (121666417521 / 1000000000000) (30416604907 / 250000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (24253 / 25600)
  have hx71 : Bounds (121666417521 / 1000000000000) (30416604907 / 250000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(48487 / 51200)
  have hx73 : Bounds (99687 / 51200) (99687 / 51200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48487 / 51200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(48487 / 51200)
  have hx74 : Bounds (99687 / 51200) (99687 / 51200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48487 / 51200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (133259149 / 200000000) (333147873 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (324321405917 / 250000000000) (81080351601 / 62500000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(48487 / 51200)
  have hx77 : Bounds (-48487 / 51200) (-48487 / 51200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48487 / 51200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2713 / 51200) (2713 / 51200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(48487 / 51200)
  have hx79 : Bounds (2713 / 51200) (2713 / 51200) x79 := by
    exact hx78
  let x80 : ℝ := -(48487 / 51200)
  have hx80 : Bounds (-48487 / 51200) (-48487 / 51200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48487 / 51200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2713 / 51200) (2713 / 51200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(48487 / 51200)
  have hx82 : Bounds (2713 / 51200) (2713 / 51200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2937684501 / 1000000000) (-183605281 / 62500000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-155662852563 / 1000000000000) (-155662852297 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (228324554221 / 200000000000) (1141622773319 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (35675711597 / 62500000000) (28540569333 / 50000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (35675711597 / 62500000000) (28540569333 / 50000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-28540569333 / 50000000000) (-35675711597 / 62500000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (6116789667 / 50000000000) (15291974431 / 125000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (6116789667 / 50000000000) (15291974431 / 125000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (48487 / 51200)
  have hx92 : Bounds (6116789667 / 50000000000) (15291974431 / 125000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (121666417521 / 1000000000000) (15291974431 / 125000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (1520830219 / 25000000000) (15291974431 / 250000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (1520830219 / 25000000000) (15291974431 / 250000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(977723 / 1000000)
  have hx98 : Bounds (1977723 / 1000000) (1977723 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977723 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(977723 / 1000000)
  have hx99 : Bounds (1977723 / 1000000) (1977723 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977723 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (340973091 / 500000000) (681946183 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1348700648903 / 1000000000000) (674350325441 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(977723 / 1000000)
  have hx102 : Bounds (-977723 / 1000000) (-977723 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977723 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (22277 / 1000000) (22277 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(977723 / 1000000)
  have hx104 : Bounds (22277 / 1000000) (22277 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(977723 / 1000000)
  have hx105 : Bounds (-977723 / 1000000) (-977723 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977723 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (22277 / 1000000) (22277 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(977723 / 1000000)
  have hx107 : Bounds (22277 / 1000000) (22277 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1902100263 / 500000000) (-95105013 / 25000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-42373087559 / 500000000000) (-10593271873 / 125000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (252790894757 / 200000000000) (631977237949 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (157994309223 / 250000000000) (631977237949 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (157994309223 / 250000000000) (631977237949 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-631977237949 / 1000000000000) (-157994309223 / 250000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (61169942051 / 1000000000000) (15292486027 / 250000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (61169942051 / 1000000000000) (15292486027 / 250000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (977723 / 1000000)
  have hx117 : Bounds (61169942051 / 1000000000000) (15292486027 / 250000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(488937 / 500000)
  have hx119 : Bounds (988937 / 500000) (988937 / 500000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((488937 / 500000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(488937 / 500000)
  have hx120 : Bounds (988937 / 500000) (988937 / 500000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((488937 / 500000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (68202253 / 100000000) (682022531 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1348954629501 / 1000000000000) (33723865787 / 25000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(488937 / 500000)
  have hx123 : Bounds (-488937 / 500000) (-488937 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((488937 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (11063 / 500000) (11063 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(488937 / 500000)
  have hx125 : Bounds (11063 / 500000) (11063 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := -(488937 / 500000)
  have hx126 : Bounds (-488937 / 500000) (-488937 / 500000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((488937 / 500000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (11063 / 500000) (11063 / 500000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(488937 / 500000)
  have hx128 : Bounds (11063 / 500000) (11063 / 500000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1905500947 / 500000000) (-119093809 / 31250000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-84322227907 / 1000000000000) (-84322227773 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (632316200797 / 500000000000) (1264632403707 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (632316200797 / 1000000000000) (316158100927 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (632316200797 / 1000000000000) (316158100927 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-316158100927 / 500000000000) (-632316200797 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (30415489073 / 500000000000) (60830980203 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (30415489073 / 500000000000) (60830980203 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (488937 / 500000)
  have hx138 : Bounds (30415489073 / 500000000000) (60830980203 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (977723 / 1000000) (488937 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (488937 / 500000) ≤ (60830980203 / 1000000000000) := hx138.2
      have h2 : (1520830219 / 25000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (15291974431 / 250000000000) := hx96.2
      have h2 : (61169942051 / 1000000000000) ≤ biasE (977723 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (205403887429 / 200000000000) (41088607341 / 40000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (3123844391 / 50000000000) (62832593287 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (3123844391 / 50000000000) (62832593287 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(122201 / 125000)
  have hx143 : Bounds (247201 / 125000) (247201 / 125000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((122201 / 125000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(122201 / 125000)
  have hx144 : Bounds (247201 / 125000) (247201 / 125000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((122201 / 125000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (681888033 / 1000000000) (340944017 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (269701445833 / 200000000000) (1348507231143 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(122201 / 125000)
  have hx147 : Bounds (-122201 / 125000) (-122201 / 125000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((122201 / 125000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (2799 / 125000) (2799 / 125000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(122201 / 125000)
  have hx149 : Bounds (2799 / 125000) (2799 / 125000) x149 := by
    exact hx148
  let x150 : ℝ := -(122201 / 125000)
  have hx150 : Bounds (-122201 / 125000) (-122201 / 125000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((122201 / 125000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (2799 / 125000) (2799 / 125000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(122201 / 125000)
  have hx152 : Bounds (2799 / 125000) (2799 / 125000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3799051529 / 1000000000) (-3799051523 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-42534180919 / 500000000000) (-85068361703 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1263438867327 / 1000000000000) (3948246467 / 3125000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (631719433663 / 1000000000000) (3948246467 / 6250000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (631719433663 / 1000000000000) (3948246467 / 6250000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-3948246467 / 6250000000) (-631719433663 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (23995213 / 390625000) (61427747337 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (23995213 / 390625000) (61427747337 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (122201 / 125000)
  have hx162 : Bounds (23995213 / 390625000) (61427747337 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(6111 / 6250)
  have hx164 : Bounds (12361 / 6250) (12361 / 6250) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6111 / 6250) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(6111 / 6250)
  have hx165 : Bounds (12361 / 6250) (12361 / 6250) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6111 / 6250) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (681964891 / 1000000000) (170491223 / 250000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (168595360353 / 125000000000) (674381442401 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(6111 / 6250)
  have hx168 : Bounds (-6111 / 6250) (-6111 / 6250) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6111 / 6250) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (139 / 6250) (139 / 6250) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(6111 / 6250)
  have hx170 : Bounds (139 / 6250) (139 / 6250) x170 := by
    exact hx169
  let x171 : ℝ := -(6111 / 6250)
  have hx171 : Bounds (-6111 / 6250) (-6111 / 6250) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6111 / 6250) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (139 / 6250) (139 / 6250) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(6111 / 6250)
  have hx173 : Bounds (139 / 6250) (139 / 6250) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-951465703 / 250000000) (-1902931403 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-84642388939 / 1000000000000) (-16928477761 / 200000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (252824098777 / 200000000000) (1264120495997 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (316030123471 / 500000000000) (632060247999 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (316030123471 / 500000000000) (632060247999 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-632060247999 / 1000000000000) (-316030123471 / 500000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (61086932001 / 1000000000000) (30543467029 / 500000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (61086932001 / 1000000000000) (30543467029 / 500000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (6111 / 6250)
  have hx183 : Bounds (61086932001 / 1000000000000) (30543467029 / 500000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(122201 / 125000)
  have hx184 : Bounds (61077905347 / 1000000000000) (61425645859 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((122201 / 125000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(6111 / 6250)
  have hx185 : Bounds (30543700917 / 500000000000) (61435196413 / 1000000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((6111 / 6250) : ℝ)) <;> norm_num
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
  have hc : Bounds (122201 / 125000) (6111 / 6250) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (122201 / 125000) ≤ (61425645859 / 1000000000000) := hx184.2
      have h2 : (23995213 / 390625000) ≤ biasE (122201 / 125000) := hx162.1
      linarith
    · have h1 : biasE (6111 / 6250) ≤ (30543467029 / 500000000000) := hx183.2
      have h2 : (30543700917 / 500000000000) ≤ x141 * (6111 / 6250) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1977723 / 1000000) (988937 / 500000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-488937 / 500000) (-977723 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (11063 / 500000) (22277 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (11063 / 500000) (22277 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (44889347757777 / 1000000000000) (45195697369611 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (44389347757777 / 500000000000) (44695697369611 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (44389347757777 / 500000000000) (44695697369611 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (2243073351 / 500000000) (179720977 / 40000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (2243073351 / 1000000000) (179720977 / 80000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (2243073351 / 1000000000) (179720977 / 80000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (247201 / 125000) (12361 / 6250) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-6111 / 6250) (-122201 / 125000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (139 / 6250) (2799 / 125000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (139 / 6250) (2799 / 125000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (11164701679171 / 250000000000) (44964028776979 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (11039701679171 / 125000000000) (44464028776979 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (11039701679171 / 125000000000) (44464028776979 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (1120234889 / 250000000) (560978463 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (1120234889 / 500000000) (560978463 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (1120234889 / 500000000) (560978463 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (17509686421 / 125000000000) (70438990451 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (1520830219 / 12500000000) (15291974431 / 125000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-15291974431 / 125000000000) (-1520830219 / 12500000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (221771199 / 12500000000) (9605781691 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (221771199 / 12500000000) (9605781691 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2193104405959 / 1000000000000) (2196805883287 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2196805883287 / 1000000000000) (-2193104405959 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2179064187367 / 1000000000000) (-2173892842577 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2179064187367 / 1000000000000) (-2173892842577 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (436222091327 / 200000000000) (1092439817029 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (511567317 / 250000000000) (10986791481 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1347 / 102400) (2713 / 204800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1347 / 102400) ≤ m → m ≤ (2713 / 204800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (2713 / 204800) (683 / 51200) m) :
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
  have hx0 : Bounds (2713 / 102400) (683 / 25600) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-683 / 25600) (-2713 / 102400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (24917 / 25600) (99687 / 102400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (24917 / 25600) (99687 / 102400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (2713 / 51200) (683 / 12800) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-683 / 12800) (-2713 / 51200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (12117 / 12800) (48487 / 51200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (12117 / 12800) (48487 / 51200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(99687 / 102400)
  have hx9 : Bounds (202087 / 102400) (202087 / 102400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99687 / 102400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(99687 / 102400)
  have hx10 : Bounds (202087 / 102400) (202087 / 102400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99687 / 102400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (135962317 / 200000000) (339905793 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (335403036567 / 250000000000) (1341612148243 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(99687 / 102400)
  have hx13 : Bounds (-99687 / 102400) (-99687 / 102400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99687 / 102400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (2713 / 102400) (2713 / 102400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(99687 / 102400)
  have hx15 : Bounds (2713 / 102400) (2713 / 102400) x15 := by
    exact hx14
  let x16 : ℝ := -(99687 / 102400)
  have hx16 : Bounds (-99687 / 102400) (-99687 / 102400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99687 / 102400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (2713 / 102400) (2713 / 102400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(99687 / 102400)
  have hx18 : Bounds (2713 / 102400) (2713 / 102400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1815415841 / 500000000) (-907707919 / 250000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-96195765169 / 1000000000000) (-96195765009 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1245416381099 / 1000000000000) (622708191617 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (622708190549 / 1000000000000) (622708191617 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (622708190549 / 1000000000000) (622708191617 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-622708191617 / 1000000000000) (-622708190549 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (70438988383 / 1000000000000) (70438990451 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (70438988383 / 1000000000000) (70438990451 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (99687 / 102400)
  have hx28 : Bounds (70438988383 / 1000000000000) (70438990451 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(24917 / 25600)
  have hx30 : Bounds (50517 / 25600) (50517 / 25600) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24917 / 25600) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(24917 / 25600)
  have hx31 : Bounds (50517 / 25600) (50517 / 25600) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24917 / 25600) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (679717561 / 1000000000) (339858781 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (335325117471 / 250000000000) (670650235929 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(24917 / 25600)
  have hx34 : Bounds (-24917 / 25600) (-24917 / 25600) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24917 / 25600) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (683 / 25600) (683 / 25600) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(24917 / 25600)
  have hx36 : Bounds (683 / 25600) (683 / 25600) x36 := by
    exact hx35
  let x37 : ℝ := -(24917 / 25600)
  have hx37 : Bounds (-24917 / 25600) (-24917 / 25600) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24917 / 25600) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (683 / 25600) (683 / 25600) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(24917 / 25600)
  have hx39 : Bounds (683 / 25600) (683 / 25600) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1811926387 / 500000000) (-113245399 / 31250000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-96683259557 / 1000000000000) (-24170814849 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1244617210327 / 1000000000000) (622308606231 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (622308605163 / 1000000000000) (622308606231 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (622308605163 / 1000000000000) (622308606231 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-622308606231 / 1000000000000) (-622308605163 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (70838573769 / 1000000000000) (70838575837 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (70838573769 / 1000000000000) (70838575837 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (24917 / 25600)
  have hx49 : Bounds (70838573769 / 1000000000000) (70838575837 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (70438988383 / 1000000000000) (70838575837 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(48487 / 51200)
  have hx52 : Bounds (99687 / 51200) (99687 / 51200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48487 / 51200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(48487 / 51200)
  have hx53 : Bounds (99687 / 51200) (99687 / 51200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48487 / 51200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (133259149 / 200000000) (333147873 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (324321405917 / 250000000000) (81080351601 / 62500000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(48487 / 51200)
  have hx56 : Bounds (-48487 / 51200) (-48487 / 51200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48487 / 51200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2713 / 51200) (2713 / 51200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(48487 / 51200)
  have hx58 : Bounds (2713 / 51200) (2713 / 51200) x58 := by
    exact hx57
  let x59 : ℝ := -(48487 / 51200)
  have hx59 : Bounds (-48487 / 51200) (-48487 / 51200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48487 / 51200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2713 / 51200) (2713 / 51200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(48487 / 51200)
  have hx61 : Bounds (2713 / 51200) (2713 / 51200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2937684501 / 1000000000) (-183605281 / 62500000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-155662852563 / 1000000000000) (-155662852297 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (228324554221 / 200000000000) (1141622773319 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (35675711597 / 62500000000) (28540569333 / 50000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (35675711597 / 62500000000) (28540569333 / 50000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-28540569333 / 50000000000) (-35675711597 / 62500000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (6116789667 / 50000000000) (15291974431 / 125000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (6116789667 / 50000000000) (15291974431 / 125000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (48487 / 51200)
  have hx71 : Bounds (6116789667 / 50000000000) (15291974431 / 125000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(12117 / 12800)
  have hx73 : Bounds (24917 / 12800) (24917 / 12800) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12117 / 12800) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(12117 / 12800)
  have hx74 : Bounds (24917 / 12800) (24917 / 12800) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12117 / 12800) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (66610513 / 100000000) (666105131 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (648333653289 / 500000000000) (648333654263 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(12117 / 12800)
  have hx77 : Bounds (-12117 / 12800) (-12117 / 12800) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12117 / 12800) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (683 / 12800) (683 / 12800) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(12117 / 12800)
  have hx79 : Bounds (683 / 12800) (683 / 12800) x79 := by
    exact hx78
  let x80 : ℝ := -(12117 / 12800)
  have hx80 : Bounds (-12117 / 12800) (-12117 / 12800) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12117 / 12800) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (683 / 12800) (683 / 12800) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(12117 / 12800)
  have hx82 : Bounds (683 / 12800) (683 / 12800) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2930705593 / 1000000000) (-732676397 / 250000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-38178862 / 244140625) (-39095154621 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (570143343913 / 500000000000) (570143345021 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (570143343913 / 1000000000000) (570143345021 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (570143343913 / 1000000000000) (570143345021 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-570143345021 / 1000000000000) (-570143343913 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (123003834979 / 1000000000000) (123003837087 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (123003834979 / 1000000000000) (123003837087 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (12117 / 12800)
  have hx92 : Bounds (123003834979 / 1000000000000) (123003837087 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (6116789667 / 50000000000) (123003837087 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (6116789667 / 100000000000) (3843869909 / 62500000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (6116789667 / 100000000000) (3843869909 / 62500000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(488787 / 500000)
  have hx98 : Bounds (988787 / 500000) (988787 / 500000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((488787 / 500000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(488787 / 500000)
  have hx99 : Bounds (988787 / 500000) (988787 / 500000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((488787 / 500000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (17046771 / 25000000) (681870841 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (674225022271 / 500000000000) (33711251163 / 25000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(488787 / 500000)
  have hx102 : Bounds (-488787 / 500000) (-488787 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((488787 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (11213 / 500000) (11213 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(488787 / 500000)
  have hx104 : Bounds (11213 / 500000) (11213 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := -(488787 / 500000)
  have hx105 : Bounds (-488787 / 500000) (-488787 / 500000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((488787 / 500000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (11213 / 500000) (11213 / 500000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(488787 / 500000)
  have hx107 : Bounds (11213 / 500000) (11213 / 500000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1898767141 / 500000000) (-949383569 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-85163503809 / 1000000000000) (-85163503673 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1263286540733 / 1000000000000) (1263286542847 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (315821635183 / 500000000000) (2467356529 / 3906250000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (315821635183 / 500000000000) (2467356529 / 3906250000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-2467356529 / 3906250000) (-315821635183 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (1921997143 / 31250000000) (30751955317 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (1921997143 / 31250000000) (30751955317 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (488787 / 500000)
  have hx117 : Bounds (1921997143 / 31250000000) (30751955317 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(244431 / 250000)
  have hx119 : Bounds (494431 / 250000) (494431 / 250000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244431 / 250000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(244431 / 250000)
  have hx120 : Bounds (494431 / 250000) (494431 / 250000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((244431 / 250000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (10655417 / 15625000) (681946689 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (674351165789 / 500000000000) (337175583389 / 250000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(244431 / 250000)
  have hx123 : Bounds (-244431 / 250000) (-244431 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244431 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (5569 / 250000) (5569 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(244431 / 250000)
  have hx125 : Bounds (5569 / 250000) (5569 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := -(244431 / 250000)
  have hx126 : Bounds (-244431 / 250000) (-244431 / 250000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((244431 / 250000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (5569 / 250000) (5569 / 250000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(244431 / 250000)
  have hx128 : Bounds (5569 / 250000) (5569 / 250000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-475530677 / 125000000) (-380424541 / 100000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-84743370887 / 1000000000000) (-84743370753 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1263958960691 / 1000000000000) (1263958962803 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (126395896069 / 200000000000) (315989740701 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (126395896069 / 200000000000) (315989740701 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-315989740701 / 500000000000) (-126395896069 / 200000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (30583849299 / 500000000000) (12233540131 / 200000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (30583849299 / 500000000000) (12233540131 / 200000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (244431 / 250000)
  have hx138 : Bounds (30583849299 / 500000000000) (12233540131 / 200000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (488787 / 500000) (244431 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (244431 / 250000) ≤ (12233540131 / 200000000000) := hx138.2
      have h2 : (6116789667 / 100000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (3843869909 / 62500000000) := hx96.2
      have h2 : (1921997143 / 31250000000) ≤ biasE (488787 / 500000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (256803795881 / 250000000000) (128426375567 / 125000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (62832592203 / 1000000000000) (63187747913 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (62832592203 / 1000000000000) (63187747913 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(488729 / 500000)
  have hx143 : Bounds (988729 / 500000) (988729 / 500000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((488729 / 500000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(488729 / 500000)
  have hx144 : Bounds (988729 / 500000) (988729 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((488729 / 500000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (681812181 / 1000000000) (340906091 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (269650990363 / 200000000000) (674127476897 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(488729 / 500000)
  have hx147 : Bounds (-488729 / 500000) (-488729 / 500000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((488729 / 500000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (11271 / 500000) (11271 / 500000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(488729 / 500000)
  have hx149 : Bounds (11271 / 500000) (11271 / 500000) x149 := by
    exact hx148
  let x150 : ℝ := -(488729 / 500000)
  have hx150 : Bounds (-488729 / 500000) (-488729 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((488729 / 500000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (11271 / 500000) (11271 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(488729 / 500000)
  have hx152 : Bounds (11271 / 500000) (11271 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-1896187523 / 500000000) (-2962793 / 781250) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-85487718287 / 1000000000000) (-85487718151 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (157845904191 / 125000000000) (1262767235643 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (157845904191 / 250000000000) (315691808911 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (157845904191 / 250000000000) (315691808911 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-315691808911 / 500000000000) (-157845904191 / 250000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (30881781089 / 500000000000) (15440891059 / 250000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (30881781089 / 500000000000) (15440891059 / 250000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (488729 / 500000)
  have hx162 : Bounds (30881781089 / 500000000000) (15440891059 / 250000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(977609 / 1000000)
  have hx164 : Bounds (1977609 / 1000000) (1977609 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977609 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(977609 / 1000000)
  have hx165 : Bounds (1977609 / 1000000) (1977609 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977609 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (681888539 / 1000000000) (34094427 / 50000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1348508911723 / 1000000000000) (1348508913701 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(977609 / 1000000)
  have hx168 : Bounds (-977609 / 1000000) (-977609 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977609 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (22391 / 1000000) (22391 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(977609 / 1000000)
  have hx170 : Bounds (22391 / 1000000) (22391 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(977609 / 1000000)
  have hx171 : Bounds (-977609 / 1000000) (-977609 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977609 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (22391 / 1000000) (22391 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(977609 / 1000000)
  have hx173 : Bounds (22391 / 1000000) (22391 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-3799096189 / 1000000000) (-3799096183 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-5316597673 / 62500000000) (-85065562633 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (252688669791 / 200000000000) (315860837767 / 250000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (631721674477 / 1000000000000) (315860837767 / 500000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (631721674477 / 1000000000000) (315860837767 / 500000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-315860837767 / 500000000000) (-631721674477 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (30712752233 / 500000000000) (61425506523 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (30712752233 / 500000000000) (61425506523 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (977609 / 1000000)
  have hx183 : Bounds (30712752233 / 500000000000) (61425506523 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(488729 / 500000)
  have hx184 : Bounds (61416219909 / 1000000000000) (617633697 / 10000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((488729 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(977609 / 1000000)
  have hx185 : Bounds (6142570763 / 100000000000) (1235458221 / 20000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((977609 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (488729 / 500000) (977609 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (488729 / 500000) ≤ (617633697 / 10000000000) := hx184.2
      have h2 : (30881781089 / 500000000000) ≤ biasE (488729 / 500000) := hx162.1
      linarith
    · have h1 : biasE (977609 / 1000000) ≤ (61425506523 / 1000000000000) := hx183.2
      have h2 : (6142570763 / 100000000000) ≤ x141 * (977609 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (988787 / 500000) (494431 / 250000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-244431 / 250000) (-488787 / 500000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (5569 / 250000) (11213 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (5569 / 250000) (11213 / 500000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (11147774904129 / 250000000000) (22445681450889 / 500000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (11022774904129 / 125000000000) (22195681450889 / 250000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (11022774904129 / 125000000000) (22195681450889 / 250000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1119851279 / 250000000) (897238421 / 200000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1119851279 / 500000000) (897238421 / 400000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1119851279 / 500000000) (897238421 / 400000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (988729 / 500000) (1977609 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-977609 / 1000000) (-488729 / 500000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (22391 / 1000000) (11271 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (22391 / 1000000) (11271 / 500000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (44361636057137 / 1000000000000) (22330400607387 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (43861636057137 / 500000000000) (22080400607387 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (43861636057137 / 500000000000) (22080400607387 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (4474187221 / 1000000000) (4480984729 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (4474187221 / 2000000000) (4480984729 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (4474187221 / 2000000000) (4480984729 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (70438988383 / 500000000000) (70838575837 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (6116789667 / 50000000000) (3843869909 / 31250000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-3843869909 / 31250000000) (-6116789667 / 50000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (8937069839 / 500000000000) (9670679167 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (8937069839 / 500000000000) (9670679167 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1094737494217 / 500000000000) (438625768967 / 200000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-438625768967 / 200000000000) (-1094737494217 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2175254705157 / 1000000000000) (-21701336301 / 10000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2175254705157 / 1000000000000) (-21701336301 / 10000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2177408652063 / 1000000000000) (1090566222363 / 500000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1076973453 / 500000000000) (5499407313 / 500000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (2713 / 204800) (683 / 51200) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (2713 / 204800) ≤ m → m ≤ (683 / 51200) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (683 / 51200) (2751 / 204800) m) :
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
  have hx0 : Bounds (683 / 25600) (2751 / 102400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-2751 / 102400) (-683 / 25600) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (99649 / 102400) (24917 / 25600) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (99649 / 102400) (24917 / 25600) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (683 / 12800) (2751 / 51200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-2751 / 51200) (-683 / 12800) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (48449 / 51200) (12117 / 12800) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (48449 / 51200) (12117 / 12800) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(24917 / 25600)
  have hx9 : Bounds (50517 / 25600) (50517 / 25600) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24917 / 25600) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(24917 / 25600)
  have hx10 : Bounds (50517 / 25600) (50517 / 25600) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24917 / 25600) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (679717561 / 1000000000) (339858781 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (335325117471 / 250000000000) (670650235929 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(24917 / 25600)
  have hx13 : Bounds (-24917 / 25600) (-24917 / 25600) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24917 / 25600) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (683 / 25600) (683 / 25600) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(24917 / 25600)
  have hx15 : Bounds (683 / 25600) (683 / 25600) x15 := by
    exact hx14
  let x16 : ℝ := -(24917 / 25600)
  have hx16 : Bounds (-24917 / 25600) (-24917 / 25600) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24917 / 25600) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (683 / 25600) (683 / 25600) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(24917 / 25600)
  have hx18 : Bounds (683 / 25600) (683 / 25600) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1811926387 / 500000000) (-113245399 / 31250000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-96683259557 / 1000000000000) (-24170814849 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1244617210327 / 1000000000000) (622308606231 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (622308605163 / 1000000000000) (622308606231 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (622308605163 / 1000000000000) (622308606231 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-622308606231 / 1000000000000) (-622308605163 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (70838573769 / 1000000000000) (70838575837 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (70838573769 / 1000000000000) (70838575837 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (24917 / 25600)
  have hx28 : Bounds (70838573769 / 1000000000000) (70838575837 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(99649 / 102400)
  have hx30 : Bounds (202049 / 102400) (202049 / 102400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99649 / 102400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(99649 / 102400)
  have hx31 : Bounds (202049 / 102400) (202049 / 102400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99649 / 102400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (679623529 / 1000000000) (67962353 / 100000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (670494406303 / 500000000000) (67049440729 / 50000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(99649 / 102400)
  have hx34 : Bounds (-99649 / 102400) (-99649 / 102400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99649 / 102400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (2751 / 102400) (2751 / 102400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(99649 / 102400)
  have hx36 : Bounds (2751 / 102400) (2751 / 102400) x36 := by
    exact hx35
  let x37 : ℝ := -(99649 / 102400)
  have hx37 : Bounds (-99649 / 102400) (-99649 / 102400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99649 / 102400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (2751 / 102400) (2751 / 102400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(99649 / 102400)
  have hx39 : Bounds (2751 / 102400) (2751 / 102400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-3616922233 / 1000000000) (-3616922227 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-48584731753 / 500000000000) (-6073091459 / 62500000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (12438193491 / 10000000000) (310954837809 / 250000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (12438193491 / 20000000000) (310954837809 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (12438193491 / 20000000000) (310954837809 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-310954837809 / 500000000000) (-12438193491 / 20000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (35618752191 / 500000000000) (1424750129 / 20000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (35618752191 / 500000000000) (1424750129 / 20000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (99649 / 102400)
  have hx49 : Bounds (35618752191 / 500000000000) (1424750129 / 20000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (70838573769 / 1000000000000) (1424750129 / 20000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(12117 / 12800)
  have hx52 : Bounds (24917 / 12800) (24917 / 12800) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12117 / 12800) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(12117 / 12800)
  have hx53 : Bounds (24917 / 12800) (24917 / 12800) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12117 / 12800) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (66610513 / 100000000) (666105131 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (648333653289 / 500000000000) (648333654263 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(12117 / 12800)
  have hx56 : Bounds (-12117 / 12800) (-12117 / 12800) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12117 / 12800) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (683 / 12800) (683 / 12800) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(12117 / 12800)
  have hx58 : Bounds (683 / 12800) (683 / 12800) x58 := by
    exact hx57
  let x59 : ℝ := -(12117 / 12800)
  have hx59 : Bounds (-12117 / 12800) (-12117 / 12800) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12117 / 12800) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (683 / 12800) (683 / 12800) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(12117 / 12800)
  have hx61 : Bounds (683 / 12800) (683 / 12800) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2930705593 / 1000000000) (-732676397 / 250000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-38178862 / 244140625) (-39095154621 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (570143343913 / 500000000000) (570143345021 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (570143343913 / 1000000000000) (570143345021 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (570143343913 / 1000000000000) (570143345021 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-570143345021 / 1000000000000) (-570143343913 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (123003834979 / 1000000000000) (123003837087 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (123003834979 / 1000000000000) (123003837087 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (12117 / 12800)
  have hx71 : Bounds (123003834979 / 1000000000000) (123003837087 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(48449 / 51200)
  have hx73 : Bounds (99649 / 51200) (99649 / 51200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48449 / 51200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(48449 / 51200)
  have hx74 : Bounds (99649 / 51200) (99649 / 51200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48449 / 51200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (665914479 / 1000000000) (8323931 / 12500000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (259209812179 / 200000000000) (1296049062843 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(48449 / 51200)
  have hx77 : Bounds (-48449 / 51200) (-48449 / 51200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48449 / 51200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2751 / 51200) (2751 / 51200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(48449 / 51200)
  have hx79 : Bounds (2751 / 51200) (2751 / 51200) x79 := by
    exact hx78
  let x80 : ℝ := -(48449 / 51200)
  have hx80 : Bounds (-48449 / 51200) (-48449 / 51200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48449 / 51200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2751 / 51200) (2751 / 51200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(48449 / 51200)
  have hx82 : Bounds (2751 / 51200) (2751 / 51200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-730943763 / 250000000) (-2923775047 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-4909243877 / 31250000000) (-78547901897 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (1138953256831 / 1000000000000) (1138953259049 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (113895325683 / 200000000000) (22779065181 / 40000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (113895325683 / 200000000000) (22779065181 / 40000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-22779065181 / 40000000000) (-113895325683 / 200000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (4946822019 / 40000000000) (24734110517 / 200000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (4946822019 / 40000000000) (24734110517 / 200000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (48449 / 51200)
  have hx92 : Bounds (4946822019 / 40000000000) (24734110517 / 200000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (123003834979 / 1000000000000) (24734110517 / 200000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (61501917489 / 1000000000000) (61835276293 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (61501917489 / 1000000000000) (61835276293 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(39097 / 40000)
  have hx98 : Bounds (79097 / 40000) (79097 / 40000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((39097 / 40000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(39097 / 40000)
  have hx99 : Bounds (79097 / 40000) (79097 / 40000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((39097 / 40000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (681795493 / 1000000000) (340897747 / 500000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (269639890549 / 200000000000) (1348199454723 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(39097 / 40000)
  have hx102 : Bounds (-39097 / 40000) (-39097 / 40000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((39097 / 40000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (903 / 40000) (903 / 40000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(39097 / 40000)
  have hx104 : Bounds (903 / 40000) (903 / 40000) x104 := by
    exact hx103
  let x105 : ℝ := -(39097 / 40000)
  have hx105 : Bounds (-39097 / 40000) (-39097 / 40000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((39097 / 40000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (903 / 40000) (903 / 40000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(39097 / 40000)
  have hx107 : Bounds (903 / 40000) (903 / 40000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1895456091 / 500000000) (-236932011 / 62500000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-85579842509 / 1000000000000) (-85579842373 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (315654902559 / 250000000000) (25252392247 / 20000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (315654902559 / 500000000000) (25252392247 / 40000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (315654902559 / 500000000000) (25252392247 / 40000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-25252392247 / 40000000000) (-315654902559 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (2473494953 / 40000000000) (30918687941 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (2473494953 / 40000000000) (30918687941 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (39097 / 40000)
  have hx117 : Bounds (2473494953 / 40000000000) (30918687941 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(39103 / 40000)
  have hx119 : Bounds (79103 / 40000) (79103 / 40000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((39103 / 40000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(39103 / 40000)
  have hx120 : Bounds (79103 / 40000) (79103 / 40000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((39103 / 40000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (340935673 / 500000000) (681871347 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (269690345413 / 200000000000) (337112932261 / 250000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(39103 / 40000)
  have hx123 : Bounds (-39103 / 40000) (-39103 / 40000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((39103 / 40000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (897 / 40000) (897 / 40000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(39103 / 40000)
  have hx125 : Bounds (897 / 40000) (897 / 40000) x125 := by
    exact hx124
  let x126 : ℝ := -(39103 / 40000)
  have hx126 : Bounds (-39103 / 40000) (-39103 / 40000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((39103 / 40000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (897 / 40000) (897 / 40000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(39103 / 40000)
  have hx128 : Bounds (897 / 40000) (897 / 40000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1898789437 / 500000000) (-949394717 / 250000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-13625713 / 160000000) (-42580353057 / 500000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (252658204163 / 200000000000) (126329102293 / 100000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (631645510407 / 1000000000000) (126329102293 / 200000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (631645510407 / 1000000000000) (126329102293 / 200000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-126329102293 / 200000000000) (-631645510407 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (12300333707 / 200000000000) (61501670593 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (12300333707 / 200000000000) (61501670593 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (39103 / 40000)
  have hx138 : Bounds (12300333707 / 200000000000) (61501670593 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (39097 / 40000) (39103 / 40000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (39103 / 40000) ≤ (61501670593 / 1000000000000) := hx138.2
      have h2 : (61501917489 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (61835276293 / 1000000000000) := hx96.2
      have h2 : (2473494953 / 40000000000) ≤ biasE (39097 / 40000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (205482200907 / 200000000000) (51380345011 / 50000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (15796936707 / 250000000000) (15885589149 / 250000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (15796936707 / 250000000000) (15885589149 / 250000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(977307 / 1000000)
  have hx143 : Bounds (1977307 / 1000000) (1977307 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977307 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(977307 / 1000000)
  have hx144 : Bounds (1977307 / 1000000) (1977307 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977307 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (681735817 / 1000000000) (340867909 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (42125031347 / 31250000000) (1348001005083 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(977307 / 1000000)
  have hx147 : Bounds (-977307 / 1000000) (-977307 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977307 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (22693 / 1000000) (22693 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(977307 / 1000000)
  have hx149 : Bounds (22693 / 1000000) (22693 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(977307 / 1000000)
  have hx150 : Bounds (-977307 / 1000000) (-977307 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977307 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (22693 / 1000000) (22693 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(977307 / 1000000)
  have hx152 : Bounds (22693 / 1000000) (22693 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-151427951 / 40000000) (-3785698769 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-42954431151 / 500000000000) (-21477215541 / 250000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (631046070401 / 500000000000) (1262092142919 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (631046070401 / 1000000000000) (31552303573 / 50000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (631046070401 / 1000000000000) (31552303573 / 50000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-31552303573 / 50000000000) (-631046070401 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (3105055427 / 50000000000) (62101110599 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (3105055427 / 50000000000) (62101110599 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (977307 / 1000000)
  have hx162 : Bounds (3105055427 / 50000000000) (62101110599 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(977459 / 1000000)
  have hx164 : Bounds (1977459 / 1000000) (1977459 / 1000000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977459 / 1000000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(977459 / 1000000)
  have hx165 : Bounds (1977459 / 1000000) (1977459 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((977459 / 1000000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (681812687 / 1000000000) (42613293 / 62500000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (674128317111 / 500000000000) (6741283181 / 5000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(977459 / 1000000)
  have hx168 : Bounds (-977459 / 1000000) (-977459 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977459 / 1000000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (22541 / 1000000) (22541 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(977459 / 1000000)
  have hx170 : Bounds (22541 / 1000000) (22541 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := -(977459 / 1000000)
  have hx171 : Bounds (-977459 / 1000000) (-977459 / 1000000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((977459 / 1000000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (22541 / 1000000) (22541 / 1000000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(977459 / 1000000)
  have hx173 : Bounds (22541 / 1000000) (22541 / 1000000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-237026213 / 62500000) (-1896209701 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-21371231469 / 250000000000) (-4274246287 / 50000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (631385854173 / 500000000000) (63138585523 / 50000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (631385854173 / 1000000000000) (63138585523 / 100000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (631385854173 / 1000000000000) (63138585523 / 100000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-63138585523 / 100000000000) (-631385854173 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (6176132477 / 100000000000) (61761326827 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (6176132477 / 100000000000) (61761326827 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (977459 / 1000000)
  have hx183 : Bounds (6176132477 / 100000000000) (61761326827 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(977307 / 1000000)
  have hx184 : Bounds (61753827289 / 1000000000000) (31050194949 / 500000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((977307 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(977459 / 1000000)
  have hx185 : Bounds (30881715913 / 500000000000) (3881878021 / 62500000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((977459 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (977307 / 1000000) (977459 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (977307 / 1000000) ≤ (31050194949 / 500000000000) := hx184.2
      have h2 : (3105055427 / 50000000000) ≤ biasE (977307 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (977459 / 1000000) ≤ (61761326827 / 1000000000000) := hx183.2
      have h2 : (30881715913 / 500000000000) ≤ x141 * (977459 / 1000000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (79097 / 40000) (79103 / 40000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-39103 / 40000) (-39097 / 40000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (897 / 40000) (903 / 40000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (897 / 40000) (903 / 40000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (22148394241417 / 500000000000) (44593088071349 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (21898394241417 / 250000000000) (44093088071349 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (21898394241417 / 250000000000) (44093088071349 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (4472707669 / 1000000000) (4479450221 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (4472707669 / 2000000000) (4479450221 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (4472707669 / 2000000000) (4479450221 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1977307 / 1000000) (1977459 / 1000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-977459 / 1000000) (-977307 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (22541 / 1000000) (22693 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (22541 / 1000000) (22693 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (11016613052483 / 250000000000) (22181802049599 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (10891613052483 / 125000000000) (21931802049599 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (10891613052483 / 125000000000) (21931802049599 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (2233717293 / 500000000) (139819753 / 31250000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (2233717293 / 1000000000) (139819753 / 62500000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (2233717293 / 1000000000) (139819753 / 62500000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (70838573769 / 500000000000) (1424750129 / 10000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (61501917489 / 500000000000) (61835276293 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-61835276293 / 500000000000) (-61501917489 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (2250824369 / 125000000000) (9735588961 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (2250824369 / 125000000000) (9735588961 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1092934073343 / 500000000000) (1094749637449 / 500000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1094749637449 / 500000000000) (-1092934073343 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-1085746339973 / 500000000000) (-541599242191 / 250000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-1085746339973 / 500000000000) (-541599242191 / 250000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (543426988599 / 250000000000) (2177430490939 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (44305489 / 20000000000) (441340887 / 40000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (683 / 51200) (2751 / 204800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (683 / 51200) ≤ m → m ≤ (2751 / 204800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043

end


