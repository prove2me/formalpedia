-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0065__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0065__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:38:02.371441+00:00
-- url     : https://prove2.me/theorems/ebcd5475-d0e0-4213-9875-36dca6061d37
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0065 (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0066, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0067, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0068, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0069).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0060Logs__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0066Logs__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0069Logs__5

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (63 / 4096) (3169 / 204800) m) :
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
  have hx0 : Bounds (63 / 2048) (3169 / 102400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3169 / 102400) (-63 / 2048) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (99231 / 102400) (1985 / 2048) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (99231 / 102400) (1985 / 2048) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (63 / 1024) (3169 / 51200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3169 / 51200) (-63 / 1024) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (48031 / 51200) (961 / 1024) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (48031 / 51200) (961 / 1024) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1985 / 2048)
  have hx9 : Bounds (4033 / 2048) (4033 / 2048) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1985 / 2048) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1985 / 2048)
  have hx10 : Bounds (4033 / 2048) (4033 / 2048) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1985 / 2048) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (84705851 / 125000000) (677646809 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (33361200887 / 25000000000) (26688960749 / 20000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1985 / 2048)
  have hx13 : Bounds (-1985 / 2048) (-1985 / 2048) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1985 / 2048) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (63 / 2048) (63 / 2048) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1985 / 2048)
  have hx15 : Bounds (63 / 2048) (63 / 2048) x15 := by
    exact hx14
  let x16 : ℝ := -(1985 / 2048)
  have hx16 : Bounds (-1985 / 2048) (-1985 / 2048) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1985 / 2048) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (63 / 2048) (63 / 2048) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1985 / 2048)
  have hx18 : Bounds (63 / 2048) (63 / 2048) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1740742131 / 500000000) (-108796383 / 31250000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-107096439701 / 1000000000000) (-21419287903 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1227351595779 / 1000000000000) (245470319587 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (613675797889 / 1000000000000) (76709474871 / 125000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (613675797889 / 1000000000000) (76709474871 / 125000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-76709474871 / 125000000000) (-613675797889 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (9933922629 / 125000000000) (79471383111 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (9933922629 / 125000000000) (79471383111 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1985 / 2048)
  have hx28 : Bounds (9933922629 / 125000000000) (79471383111 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(99231 / 102400)
  have hx30 : Bounds (201631 / 102400) (201631 / 102400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99231 / 102400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(99231 / 102400)
  have hx31 : Bounds (201631 / 102400) (201631 / 102400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99231 / 102400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (677552581 / 1000000000) (338776291 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (13341367623 / 10000000000) (133413676427 / 100000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(99231 / 102400)
  have hx34 : Bounds (-99231 / 102400) (-99231 / 102400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99231 / 102400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3169 / 102400) (3169 / 102400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(99231 / 102400)
  have hx36 : Bounds (3169 / 102400) (3169 / 102400) x36 := by
    exact hx35
  let x37 : ℝ := -(99231 / 102400)
  have hx37 : Bounds (-99231 / 102400) (-99231 / 102400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99231 / 102400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3169 / 102400) (3169 / 102400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(99231 / 102400)
  have hx39 : Bounds (3169 / 102400) (3169 / 102400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-695094127 / 200000000) (-3475470629 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-53778156457 / 500000000000) (-107556312727 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (613290224693 / 500000000000) (1226580451543 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (613290224693 / 1000000000000) (153322556443 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (613290224693 / 1000000000000) (153322556443 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-153322556443 / 250000000000) (-613290224693 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (19964238557 / 250000000000) (79856956307 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (19964238557 / 250000000000) (79856956307 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (99231 / 102400)
  have hx49 : Bounds (19964238557 / 250000000000) (79856956307 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (9933922629 / 125000000000) (79856956307 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(961 / 1024)
  have hx52 : Bounds (1985 / 1024) (1985 / 1024) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((961 / 1024) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(961 / 1024)
  have hx53 : Bounds (1985 / 1024) (1985 / 1024) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((961 / 1024) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (661902387 / 1000000000) (165475597 / 250000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (641541131931 / 500000000000) (1283082265801 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(961 / 1024)
  have hx56 : Bounds (-961 / 1024) (-961 / 1024) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((961 / 1024) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (63 / 1024) (63 / 1024) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(961 / 1024)
  have hx58 : Bounds (63 / 1024) (63 / 1024) x58 := by
    exact hx57
  let x59 : ℝ := -(961 / 1024)
  have hx59 : Bounds (-961 / 1024) (-961 / 1024) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((961 / 1024) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (63 / 1024) (63 / 1024) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(961 / 1024)
  have hx61 : Bounds (63 / 1024) (63 / 1024) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2788337081 / 1000000000) (-697084269 / 250000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-42887020533 / 250000000000) (-5360877557 / 31250000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (111153418173 / 100000000000) (1111534183977 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (111153418173 / 200000000000) (555767091989 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (111153418173 / 200000000000) (555767091989 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-555767091989 / 1000000000000) (-111153418173 / 200000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (137380088011 / 1000000000000) (27476018027 / 200000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (137380088011 / 1000000000000) (27476018027 / 200000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (961 / 1024)
  have hx71 : Bounds (137380088011 / 1000000000000) (27476018027 / 200000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(48031 / 51200)
  have hx73 : Bounds (99231 / 51200) (99231 / 51200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48031 / 51200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(48031 / 51200)
  have hx74 : Bounds (99231 / 51200) (99231 / 51200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48031 / 51200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (661710933 / 1000000000) (330855467 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (641232788989 / 500000000000) (641232789959 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(48031 / 51200)
  have hx77 : Bounds (-48031 / 51200) (-48031 / 51200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48031 / 51200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (3169 / 51200) (3169 / 51200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(48031 / 51200)
  have hx79 : Bounds (3169 / 51200) (3169 / 51200) x79 := by
    exact hx78
  let x80 : ℝ := -(48031 / 51200)
  have hx80 : Bounds (-48031 / 51200) (-48031 / 51200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48031 / 51200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (3169 / 51200) (3169 / 51200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(48031 / 51200)
  have hx82 : Bounds (3169 / 51200) (3169 / 51200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1391161727 / 500000000) (-2782323449 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-43052651493 / 250000000000) (-172210605661 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (555127486003 / 500000000000) (1110254974257 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (555127486003 / 1000000000000) (555127487129 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (555127486003 / 1000000000000) (555127487129 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-555127487129 / 1000000000000) (-555127486003 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (138019692871 / 1000000000000) (138019694997 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (138019692871 / 1000000000000) (138019694997 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (48031 / 51200)
  have hx92 : Bounds (138019692871 / 1000000000000) (138019694997 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (137380088011 / 1000000000000) (138019694997 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (13738008801 / 200000000000) (69009847499 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (13738008801 / 200000000000) (69009847499 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(487083 / 500000)
  have hx98 : Bounds (987083 / 500000) (987083 / 500000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487083 / 500000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(487083 / 500000)
  have hx99 : Bounds (987083 / 500000) (987083 / 500000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487083 / 500000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (68014603 / 100000000) (680146031 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (67136058373 / 50000000000) (335680292359 / 250000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(487083 / 500000)
  have hx102 : Bounds (-487083 / 500000) (-487083 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487083 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (12917 / 500000) (12917 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(487083 / 500000)
  have hx104 : Bounds (12917 / 500000) (12917 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := -(487083 / 500000)
  have hx105 : Bounds (-487083 / 500000) (-487083 / 500000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487083 / 500000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (12917 / 500000) (12917 / 500000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(487083 / 500000)
  have hx107 : Bounds (12917 / 500000) (12917 / 500000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-914015957 / 250000000) (-1828031911 / 500000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-94450752933 / 1000000000000) (-94450752777 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1248270414527 / 1000000000000) (1248270416659 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (624135207263 / 1000000000000) (62413520833 / 100000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (624135207263 / 1000000000000) (62413520833 / 100000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-62413520833 / 100000000000) (-624135207263 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (6901197167 / 100000000000) (69011973737 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (6901197167 / 100000000000) (69011973737 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (487083 / 500000)
  have hx117 : Bounds (6901197167 / 100000000000) (69011973737 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(194863 / 200000)
  have hx119 : Bounds (394863 / 200000) (394863 / 200000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194863 / 200000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(194863 / 200000)
  have hx120 : Bounds (394863 / 200000) (394863 / 200000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194863 / 200000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (340110751 / 500000000) (680221503 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1342971514721 / 1000000000000) (167871439587 / 125000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(194863 / 200000)
  have hx123 : Bounds (-194863 / 200000) (-194863 / 200000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194863 / 200000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (5137 / 200000) (5137 / 200000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(194863 / 200000)
  have hx125 : Bounds (5137 / 200000) (5137 / 200000) x125 := by
    exact hx124
  let x126 : ℝ := -(194863 / 200000)
  have hx126 : Bounds (-194863 / 200000) (-194863 / 200000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194863 / 200000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (5137 / 200000) (5137 / 200000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(194863 / 200000)
  have hx128 : Bounds (5137 / 200000) (5137 / 200000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1830924059 / 500000000) (-228865507 / 62500000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-94054568911 / 1000000000000) (-23513642189 / 250000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (124891694581 / 100000000000) (62445847397 / 50000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (124891694581 / 200000000000) (62445847397 / 100000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (124891694581 / 200000000000) (62445847397 / 100000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-62445847397 / 100000000000) (-124891694581 / 200000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (6868870603 / 100000000000) (13737741619 / 200000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (6868870603 / 100000000000) (13737741619 / 200000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (194863 / 200000)
  have hx138 : Bounds (6868870603 / 100000000000) (13737741619 / 200000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (487083 / 500000) (194863 / 200000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (194863 / 200000) ≤ (13737741619 / 200000000000) := hx138.2
      have h2 : (13738008801 / 200000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (69009847499 / 1000000000000) := hx96.2
      have h2 : (6901197167 / 100000000000) ≤ biasE (487083 / 500000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (16120906801 / 15625000000) (515967792323 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (70870131043 / 1000000000000) (35606858663 / 500000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (70870131043 / 1000000000000) (35606858663 / 500000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(243501 / 250000)
  have hx143 : Bounds (493501 / 250000) (493501 / 250000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243501 / 250000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(243501 / 250000)
  have hx144 : Bounds (493501 / 250000) (493501 / 250000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243501 / 250000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (680063967 / 1000000000) (21251999 / 31250000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1342448991113 / 1000000000000) (20975765517 / 15625000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(243501 / 250000)
  have hx147 : Bounds (-243501 / 250000) (-243501 / 250000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243501 / 250000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (6499 / 250000) (6499 / 250000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(243501 / 250000)
  have hx149 : Bounds (6499 / 250000) (6499 / 250000) x149 := by
    exact hx148
  let x150 : ℝ := -(243501 / 250000)
  have hx150 : Bounds (-243501 / 250000) (-243501 / 250000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243501 / 250000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (6499 / 250000) (6499 / 250000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(243501 / 250000)
  have hx152 : Bounds (6499 / 250000) (6499 / 250000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-1824906301 / 500000000) (-912453149 / 250000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-47440264201 / 500000000000) (-18976105649 / 200000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1247568462711 / 1000000000000) (1247568464843 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (124756846271 / 200000000000) (311892116211 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (124756846271 / 200000000000) (311892116211 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-311892116211 / 500000000000) (-124756846271 / 200000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (34681473789 / 500000000000) (13872589929 / 200000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (34681473789 / 500000000000) (13872589929 / 200000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (243501 / 250000)
  have hx162 : Bounds (34681473789 / 500000000000) (13872589929 / 200000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(487077 / 500000)
  have hx164 : Bounds (987077 / 500000) (987077 / 500000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487077 / 500000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(487077 / 500000)
  have hx165 : Bounds (987077 / 500000) (987077 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487077 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (42508747 / 62500000) (680139953 / 1000000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (3356752517 / 2500000000) (53708040351 / 40000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(487077 / 500000)
  have hx168 : Bounds (-487077 / 500000) (-487077 / 500000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487077 / 500000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (12923 / 500000) (12923 / 500000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(487077 / 500000)
  have hx170 : Bounds (12923 / 500000) (12923 / 500000) x170 := by
    exact hx169
  let x171 : ℝ := -(487077 / 500000)
  have hx171 : Bounds (-487077 / 500000) (-487077 / 500000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487077 / 500000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (12923 / 500000) (12923 / 500000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(487077 / 500000)
  have hx173 : Bounds (12923 / 500000) (12923 / 500000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-456949929 / 125000000) (-1827799713 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-2362065573 / 25000000000) (-23620655691 / 250000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (31205459597 / 25000000000) (1248218386011 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (31205459597 / 50000000000) (312054596503 / 500000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (31205459597 / 50000000000) (312054596503 / 500000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-312054596503 / 500000000000) (-31205459597 / 50000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (34518993497 / 500000000000) (3451899453 / 50000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (34518993497 / 500000000000) (3451899453 / 50000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (487077 / 500000)
  have hx183 : Bounds (34518993497 / 500000000000) (3451899453 / 50000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(243501 / 250000)
  have hx184 : Bounds (17256947779 / 250000000000) (69362445531 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((243501 / 250000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(487077 / 500000)
  have hx185 : Bounds (17259605409 / 250000000000) (17343281897 / 250000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((487077 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (243501 / 250000) (487077 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (243501 / 250000) ≤ (69362445531 / 1000000000000) := hx184.2
      have h2 : (34681473789 / 500000000000) ≤ biasE (243501 / 250000) := hx162.1
      linarith
    · have h1 : biasE (487077 / 500000) ≤ (3451899453 / 50000000000) := hx183.2
      have h2 : (17259605409 / 250000000000) ≤ x141 * (487077 / 500000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (987083 / 500000) (394863 / 200000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-194863 / 200000) (-487083 / 500000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (5137 / 200000) (12917 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (5137 / 200000) (12917 / 500000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (9677169621429 / 250000000000) (9733307377847 / 250000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (9552169621429 / 125000000000) (9608307377847 / 125000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (9552169621429 / 125000000000) (9608307377847 / 125000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (1084052463 / 250000000) (4342069621 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (1084052463 / 500000000) (4342069621 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (1084052463 / 500000000) (4342069621 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (493501 / 250000) (987077 / 500000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-487077 / 500000) (-243501 / 250000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (12923 / 500000) (6499 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (12923 / 500000) (6499 / 250000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (19233728265887 / 500000000000) (38690706492301 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (18983728265887 / 250000000000) (38190706492301 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (18983728265887 / 250000000000) (38190706492301 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (2164938281 / 500000000) (541967423 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (2164938281 / 1000000000) (541967423 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (2164938281 / 1000000000) (541967423 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (9933922629 / 62500000000) (79856956307 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (13738008801 / 100000000000) (69009847499 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-69009847499 / 500000000000) (-13738008801 / 100000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (10461533533 / 500000000000) (5583456151 / 250000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (10461533533 / 500000000000) (5583456151 / 250000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2112094103341 / 1000000000000) (2115271781393 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2115271781393 / 1000000000000) (-2112094103341 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2094348714327 / 1000000000000) (-2089760278737 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2094348714327 / 1000000000000) (-2089760278737 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (524484840239 / 250000000000) (2101182294249 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (3590646629 / 1000000000000) (1427751939 / 125000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (63 / 4096) (3169 / 204800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (63 / 4096) ≤ m → m ≤ (3169 / 204800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3169 / 204800) (797 / 51200) m) :
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
  have hx0 : Bounds (3169 / 102400) (797 / 25600) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-797 / 25600) (-3169 / 102400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (24803 / 25600) (99231 / 102400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (24803 / 25600) (99231 / 102400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3169 / 51200) (797 / 12800) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-797 / 12800) (-3169 / 51200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (12003 / 12800) (48031 / 51200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (12003 / 12800) (48031 / 51200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(99231 / 102400)
  have hx9 : Bounds (201631 / 102400) (201631 / 102400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99231 / 102400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(99231 / 102400)
  have hx10 : Bounds (201631 / 102400) (201631 / 102400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99231 / 102400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (677552581 / 1000000000) (338776291 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (13341367623 / 10000000000) (133413676427 / 100000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(99231 / 102400)
  have hx13 : Bounds (-99231 / 102400) (-99231 / 102400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99231 / 102400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3169 / 102400) (3169 / 102400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(99231 / 102400)
  have hx15 : Bounds (3169 / 102400) (3169 / 102400) x15 := by
    exact hx14
  let x16 : ℝ := -(99231 / 102400)
  have hx16 : Bounds (-99231 / 102400) (-99231 / 102400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99231 / 102400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3169 / 102400) (3169 / 102400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(99231 / 102400)
  have hx18 : Bounds (3169 / 102400) (3169 / 102400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-695094127 / 200000000) (-3475470629 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-53778156457 / 500000000000) (-107556312727 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (613290224693 / 500000000000) (1226580451543 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (613290224693 / 1000000000000) (153322556443 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (613290224693 / 1000000000000) (153322556443 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-153322556443 / 250000000000) (-613290224693 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (19964238557 / 250000000000) (79856956307 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (19964238557 / 250000000000) (79856956307 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (99231 / 102400)
  have hx28 : Bounds (19964238557 / 250000000000) (79856956307 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(24803 / 25600)
  have hx30 : Bounds (50403 / 25600) (50403 / 25600) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24803 / 25600) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(24803 / 25600)
  have hx31 : Bounds (50403 / 25600) (50403 / 25600) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24803 / 25600) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (135491669 / 200000000) (338729173 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (20841023537 / 15625000000) (666912754169 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(24803 / 25600)
  have hx34 : Bounds (-24803 / 25600) (-24803 / 25600) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24803 / 25600) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (797 / 25600) (797 / 25600) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(24803 / 25600)
  have hx36 : Bounds (797 / 25600) (797 / 25600) x36 := by
    exact hx35
  let x37 : ℝ := -(24803 / 25600)
  have hx37 : Bounds (-24803 / 25600) (-24803 / 25600) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24803 / 25600) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (797 / 25600) (797 / 25600) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(24803 / 25600)
  have hx39 : Bounds (797 / 25600) (797 / 25600) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1734746477 / 500000000) (-867373237 / 250000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-108015073607 / 1000000000000) (-5400753671 / 50000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1225810432761 / 1000000000000) (612905217459 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (30645260819 / 50000000000) (612905217459 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (30645260819 / 50000000000) (612905217459 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-612905217459 / 1000000000000) (-30645260819 / 50000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (80241962541 / 1000000000000) (4012098231 / 50000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (80241962541 / 1000000000000) (4012098231 / 50000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (24803 / 25600)
  have hx49 : Bounds (80241962541 / 1000000000000) (4012098231 / 50000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (19964238557 / 250000000000) (4012098231 / 50000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(48031 / 51200)
  have hx52 : Bounds (99231 / 51200) (99231 / 51200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48031 / 51200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(48031 / 51200)
  have hx53 : Bounds (99231 / 51200) (99231 / 51200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48031 / 51200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (661710933 / 1000000000) (330855467 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (641232788989 / 500000000000) (641232789959 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(48031 / 51200)
  have hx56 : Bounds (-48031 / 51200) (-48031 / 51200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48031 / 51200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (3169 / 51200) (3169 / 51200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(48031 / 51200)
  have hx58 : Bounds (3169 / 51200) (3169 / 51200) x58 := by
    exact hx57
  let x59 : ℝ := -(48031 / 51200)
  have hx59 : Bounds (-48031 / 51200) (-48031 / 51200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48031 / 51200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (3169 / 51200) (3169 / 51200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(48031 / 51200)
  have hx61 : Bounds (3169 / 51200) (3169 / 51200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1391161727 / 500000000) (-2782323449 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-43052651493 / 250000000000) (-172210605661 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (555127486003 / 500000000000) (1110254974257 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (555127486003 / 1000000000000) (555127487129 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (555127486003 / 1000000000000) (555127487129 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-555127487129 / 1000000000000) (-555127486003 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (138019692871 / 1000000000000) (138019694997 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (138019692871 / 1000000000000) (138019694997 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (48031 / 51200)
  have hx71 : Bounds (138019692871 / 1000000000000) (138019694997 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(12003 / 12800)
  have hx73 : Bounds (24803 / 12800) (24803 / 12800) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12003 / 12800) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(12003 / 12800)
  have hx74 : Bounds (24803 / 12800) (24803 / 12800) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12003 / 12800) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (330759721 / 500000000) (661519443 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (640924481247 / 500000000000) (80115560277 / 62500000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(12003 / 12800)
  have hx77 : Bounds (-12003 / 12800) (-12003 / 12800) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12003 / 12800) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (797 / 12800) (797 / 12800) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(12003 / 12800)
  have hx79 : Bounds (797 / 12800) (797 / 12800) x79 := by
    exact hx78
  let x80 : ℝ := -(12003 / 12800)
  have hx80 : Bounds (-12003 / 12800) (-12003 / 12800) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12003 / 12800) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (797 / 12800) (797 / 12800) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(12003 / 12800)
  have hx82 : Bounds (797 / 12800) (797 / 12800) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2776345773 / 1000000000) (-347043221 / 125000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-43217726193 / 250000000000) (-8643545223 / 50000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (554489028861 / 500000000000) (277244514993 / 250000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (554489028861 / 1000000000000) (277244514993 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (554489028861 / 1000000000000) (277244514993 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-277244514993 / 500000000000) (-554489028861 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (69329075007 / 500000000000) (138658152139 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (69329075007 / 500000000000) (138658152139 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (12003 / 12800)
  have hx92 : Bounds (69329075007 / 500000000000) (138658152139 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (138019692871 / 1000000000000) (138658152139 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (13801969287 / 200000000000) (6932907607 / 100000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (13801969287 / 200000000000) (6932907607 / 100000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(974019 / 1000000)
  have hx98 : Bounds (1974019 / 1000000) (1974019 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((974019 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(974019 / 1000000)
  have hx99 : Bounds (1974019 / 1000000) (1974019 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((974019 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (340035783 / 500000000) (680071567 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1342474192643 / 1000000000000) (671237097309 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(974019 / 1000000)
  have hx102 : Bounds (-974019 / 1000000) (-974019 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((974019 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (25981 / 1000000) (25981 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(974019 / 1000000)
  have hx104 : Bounds (25981 / 1000000) (25981 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(974019 / 1000000)
  have hx105 : Bounds (-974019 / 1000000) (-974019 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((974019 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (25981 / 1000000) (25981 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(974019 / 1000000)
  have hx107 : Bounds (25981 / 1000000) (25981 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-182519489 / 50000000) (-1825194887 / 500000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-151745243 / 1600000000) (-47420388359 / 500000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (155954176971 / 125000000000) (12476334179 / 10000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (155954176971 / 250000000000) (12476334179 / 20000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (155954176971 / 250000000000) (12476334179 / 20000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-12476334179 / 20000000000) (-155954176971 / 250000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (1386609421 / 20000000000) (17332618279 / 250000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (1386609421 / 20000000000) (17332618279 / 250000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (974019 / 1000000)
  have hx117 : Bounds (1386609421 / 20000000000) (17332618279 / 250000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(974167 / 1000000)
  have hx119 : Bounds (1974167 / 1000000) (1974167 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((974167 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(974167 / 1000000)
  have hx120 : Bounds (1974167 / 1000000) (1974167 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((974167 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (680146537 / 1000000000) (340073269 / 500000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1342722848509 / 1000000000000) (335680712621 / 250000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(974167 / 1000000)
  have hx123 : Bounds (-974167 / 1000000) (-974167 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((974167 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (25833 / 1000000) (25833 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(974167 / 1000000)
  have hx125 : Bounds (25833 / 1000000) (25833 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(974167 / 1000000)
  have hx126 : Bounds (-974167 / 1000000) (-974167 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((974167 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (25833 / 1000000) (25833 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(974167 / 1000000)
  have hx128 : Bounds (25833 / 1000000) (25833 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-3656102537 / 1000000000) (-3656102531 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-94448096839 / 1000000000000) (-94448096683 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (124827475167 / 100000000000) (1248274753801 / 1000000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (124827475167 / 200000000000) (624137376901 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (124827475167 / 200000000000) (624137376901 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-624137376901 / 1000000000000) (-124827475167 / 200000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (69009803099 / 1000000000000) (13801961033 / 200000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (69009803099 / 1000000000000) (13801961033 / 200000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (974167 / 1000000)
  have hx138 : Bounds (69009803099 / 1000000000000) (13801961033 / 200000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (974019 / 1000000) (974167 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (974167 / 1000000) ≤ (13801961033 / 200000000000) := hx138.2
      have h2 : (13801969287 / 200000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (6932907607 / 100000000000) := hx96.2
      have h2 : (1386609421 / 20000000000) ≤ biasE (974019 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (206387116929 / 200000000000) (1032133209693 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (71213716227 / 1000000000000) (7155684181 / 100000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (71213716227 / 1000000000000) (7155684181 / 100000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(486927 / 500000)
  have hx143 : Bounds (986927 / 500000) (986927 / 500000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((486927 / 500000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(486927 / 500000)
  have hx144 : Bounds (986927 / 500000) (986927 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((486927 / 500000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (84998497 / 125000000) (679987977 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1342196986379 / 1000000000000) (671098494177 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(486927 / 500000)
  have hx147 : Bounds (-486927 / 500000) (-486927 / 500000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((486927 / 500000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (13073 / 500000) (13073 / 500000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(486927 / 500000)
  have hx149 : Bounds (13073 / 500000) (13073 / 500000) x149 := by
    exact hx148
  let x150 : ℝ := -(486927 / 500000)
  have hx150 : Bounds (-486927 / 500000) (-486927 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((486927 / 500000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (13073 / 500000) (13073 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(486927 / 500000)
  have hx152 : Bounds (13073 / 500000) (13073 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3644059067 / 1000000000) (-3644059061 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-47638784183 / 500000000000) (-5954848013 / 62500000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1246919418013 / 1000000000000) (623459710073 / 500000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (311729854503 / 500000000000) (623459710073 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (311729854503 / 500000000000) (623459710073 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-623459710073 / 1000000000000) (-311729854503 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (69687469927 / 1000000000000) (34843735997 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (69687469927 / 1000000000000) (34843735997 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (486927 / 500000)
  have hx162 : Bounds (69687469927 / 1000000000000) (34843735997 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(194801 / 200000)
  have hx164 : Bounds (394801 / 200000) (394801 / 200000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194801 / 200000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(194801 / 200000)
  have hx165 : Bounds (394801 / 200000) (394801 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194801 / 200000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (680064473 / 1000000000) (340032237 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (167806333753 / 125000000000) (1342450671999 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(194801 / 200000)
  have hx168 : Bounds (-194801 / 200000) (-194801 / 200000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194801 / 200000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (5199 / 200000) (5199 / 200000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(194801 / 200000)
  have hx170 : Bounds (5199 / 200000) (5199 / 200000) x170 := by
    exact hx169
  let x171 : ℝ := -(194801 / 200000)
  have hx171 : Bounds (-194801 / 200000) (-194801 / 200000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194801 / 200000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (5199 / 200000) (5199 / 200000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(194801 / 200000)
  have hx173 : Bounds (5199 / 200000) (5199 / 200000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-364985107 / 100000000) (-456231383 / 125000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-18975575713 / 200000000000) (-11859734801 / 125000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1247572791459 / 1000000000000) (1247572793591 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (623786395729 / 1000000000000) (155946599199 / 250000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (623786395729 / 1000000000000) (155946599199 / 250000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-155946599199 / 250000000000) (-623786395729 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (17340195801 / 250000000000) (69360785271 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (17340195801 / 250000000000) (69360785271 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (194801 / 200000)
  have hx183 : Bounds (17340195801 / 250000000000) (69360785271 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(486927 / 500000)
  have hx184 : Bounds (34675881201 / 500000000000) (557487333 / 8000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((486927 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(194801 / 200000)
  have hx185 : Bounds (69362515673 / 1000000000000) (17424180427 / 250000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((194801 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (486927 / 500000) (194801 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (486927 / 500000) ≤ (557487333 / 8000000000) := hx184.2
      have h2 : (69687469927 / 1000000000000) ≤ biasE (486927 / 500000) := hx162.1
      linarith
    · have h1 : biasE (194801 / 200000) ≤ (69360785271 / 1000000000000) := hx183.2
      have h2 : (69362515673 / 1000000000000) ≤ x141 * (194801 / 200000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1974019 / 1000000) (1974167 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-974167 / 1000000) (-974019 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (25833 / 1000000) (25981 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (25833 / 1000000) (25981 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (19244832762403 / 500000000000) (38710176905509 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (18994832762403 / 250000000000) (38210176905509 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (18994832762403 / 250000000000) (38210176905509 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (216523067 / 50000000) (173449963 / 40000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (216523067 / 100000000) (173449963 / 80000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (216523067 / 100000000) (173449963 / 80000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (986927 / 500000) (394801 / 200000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-194801 / 200000) (-486927 / 500000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (5199 / 200000) (13073 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (5199 / 200000) (13073 / 500000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (38246768148091 / 1000000000000) (38468936333911 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (37746768148091 / 500000000000) (37968936333911 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (37746768148091 / 500000000000) (37968936333911 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (4324047037 / 1000000000) (541239443 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (4324047037 / 2000000000) (541239443 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (4324047037 / 2000000000) (541239443 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (19964238557 / 125000000000) (4012098231 / 25000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (13801969287 / 100000000000) (6932907607 / 50000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-6932907607 / 50000000000) (-13801969287 / 100000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (5263939079 / 250000000000) (2246423637 / 100000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (5263939079 / 250000000000) (2246423637 / 100000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1054487905981 / 500000000000) (2112115376323 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2112115376323 / 1000000000000) (-1054487905981 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2091059620007 / 1000000000000) (-260813946949 / 125000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2091059620007 / 1000000000000) (-260813946949 / 125000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2094713645677 / 1000000000000) (524489562191 / 250000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (365402567 / 100000000000) (2861668293 / 250000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3169 / 204800) (797 / 51200) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3169 / 204800) ≤ m → m ≤ (797 / 51200) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (797 / 51200) (3207 / 204800) m) :
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
  have hx0 : Bounds (797 / 25600) (3207 / 102400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3207 / 102400) (-797 / 25600) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (99193 / 102400) (24803 / 25600) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (99193 / 102400) (24803 / 25600) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (797 / 12800) (3207 / 51200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3207 / 51200) (-797 / 12800) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (47993 / 51200) (12003 / 12800) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (47993 / 51200) (12003 / 12800) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(24803 / 25600)
  have hx9 : Bounds (50403 / 25600) (50403 / 25600) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24803 / 25600) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(24803 / 25600)
  have hx10 : Bounds (50403 / 25600) (50403 / 25600) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24803 / 25600) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (135491669 / 200000000) (338729173 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (20841023537 / 15625000000) (666912754169 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(24803 / 25600)
  have hx13 : Bounds (-24803 / 25600) (-24803 / 25600) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24803 / 25600) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (797 / 25600) (797 / 25600) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(24803 / 25600)
  have hx15 : Bounds (797 / 25600) (797 / 25600) x15 := by
    exact hx14
  let x16 : ℝ := -(24803 / 25600)
  have hx16 : Bounds (-24803 / 25600) (-24803 / 25600) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24803 / 25600) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (797 / 25600) (797 / 25600) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(24803 / 25600)
  have hx18 : Bounds (797 / 25600) (797 / 25600) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1734746477 / 500000000) (-867373237 / 250000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-108015073607 / 1000000000000) (-5400753671 / 50000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1225810432761 / 1000000000000) (612905217459 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (30645260819 / 50000000000) (612905217459 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (30645260819 / 50000000000) (612905217459 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-612905217459 / 1000000000000) (-30645260819 / 50000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (80241962541 / 1000000000000) (4012098231 / 50000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (80241962541 / 1000000000000) (4012098231 / 50000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (24803 / 25600)
  have hx28 : Bounds (80241962541 / 1000000000000) (4012098231 / 50000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(99193 / 102400)
  have hx30 : Bounds (201593 / 102400) (201593 / 102400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99193 / 102400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(99193 / 102400)
  have hx31 : Bounds (201593 / 102400) (201593 / 102400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99193 / 102400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (6773641 / 10000000) (677364101 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (166689283461 / 125000000000) (666757134829 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(99193 / 102400)
  have hx34 : Bounds (-99193 / 102400) (-99193 / 102400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99193 / 102400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3207 / 102400) (3207 / 102400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(99193 / 102400)
  have hx36 : Bounds (3207 / 102400) (3207 / 102400) x36 := by
    exact hx35
  let x37 : ℝ := -(99193 / 102400)
  have hx37 : Bounds (-99193 / 102400) (-99193 / 102400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99193 / 102400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3207 / 102400) (3207 / 102400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(99193 / 102400)
  have hx39 : Bounds (3207 / 102400) (3207 / 102400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1731775397 / 500000000) (-3463550789 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-108472728481 / 1000000000000) (-108472728323 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1225041539207 / 1000000000000) (245008308267 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (612520769603 / 1000000000000) (153130192667 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (612520769603 / 1000000000000) (153130192667 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-153130192667 / 250000000000) (-612520769603 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (20156602333 / 250000000000) (80626411397 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (20156602333 / 250000000000) (80626411397 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (99193 / 102400)
  have hx49 : Bounds (20156602333 / 250000000000) (80626411397 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (80241962541 / 1000000000000) (80626411397 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(12003 / 12800)
  have hx52 : Bounds (24803 / 12800) (24803 / 12800) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12003 / 12800) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(12003 / 12800)
  have hx53 : Bounds (24803 / 12800) (24803 / 12800) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12003 / 12800) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (330759721 / 500000000) (661519443 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (640924481247 / 500000000000) (80115560277 / 62500000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(12003 / 12800)
  have hx56 : Bounds (-12003 / 12800) (-12003 / 12800) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12003 / 12800) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (797 / 12800) (797 / 12800) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(12003 / 12800)
  have hx58 : Bounds (797 / 12800) (797 / 12800) x58 := by
    exact hx57
  let x59 : ℝ := -(12003 / 12800)
  have hx59 : Bounds (-12003 / 12800) (-12003 / 12800) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12003 / 12800) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (797 / 12800) (797 / 12800) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(12003 / 12800)
  have hx61 : Bounds (797 / 12800) (797 / 12800) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2776345773 / 1000000000) (-347043221 / 125000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-43217726193 / 250000000000) (-8643545223 / 50000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (554489028861 / 500000000000) (277244514993 / 250000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (554489028861 / 1000000000000) (277244514993 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (554489028861 / 1000000000000) (277244514993 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-277244514993 / 500000000000) (-554489028861 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (69329075007 / 500000000000) (138658152139 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (69329075007 / 500000000000) (138658152139 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (12003 / 12800)
  have hx71 : Bounds (69329075007 / 500000000000) (138658152139 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(47993 / 51200)
  have hx73 : Bounds (99193 / 51200) (99193 / 51200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((47993 / 51200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(47993 / 51200)
  have hx74 : Bounds (99193 / 51200) (99193 / 51200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((47993 / 51200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (132265583 / 200000000) (165331979 / 250000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (640616209693 / 500000000000) (320308105331 / 250000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(47993 / 51200)
  have hx77 : Bounds (-47993 / 51200) (-47993 / 51200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((47993 / 51200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (3207 / 51200) (3207 / 51200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(47993 / 51200)
  have hx79 : Bounds (3207 / 51200) (3207 / 51200) x79 := by
    exact hx78
  let x80 : ℝ := -(47993 / 51200)
  have hx80 : Bounds (-47993 / 51200) (-47993 / 51200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((47993 / 51200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (3207 / 51200) (3207 / 51200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(47993 / 51200)
  have hx82 : Bounds (3207 / 51200) (3207 / 51200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2770403613 / 1000000000) (-2770403609 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-43382247983 / 250000000000) (-542278099 / 3125000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (553851713727 / 500000000000) (276925857411 / 250000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (553851713727 / 1000000000000) (276925857411 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (553851713727 / 1000000000000) (276925857411 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-276925857411 / 500000000000) (-553851713727 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (69647732589 / 500000000000) (139295467273 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (69647732589 / 500000000000) (139295467273 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (47993 / 51200)
  have hx92 : Bounds (69647732589 / 500000000000) (139295467273 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (69329075007 / 500000000000) (139295467273 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (69329075007 / 1000000000000) (69647733637 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (69329075007 / 1000000000000) (69647733637 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(60867 / 62500)
  have hx98 : Bounds (123367 / 62500) (123367 / 62500) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((60867 / 62500) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(60867 / 62500)
  have hx99 : Bounds (123367 / 62500) (123367 / 62500) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((60867 / 62500) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (135999419 / 200000000) (84999637 / 125000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1342227225901 / 1000000000000) (335556806969 / 250000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(60867 / 62500)
  have hx102 : Bounds (-60867 / 62500) (-60867 / 62500) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((60867 / 62500) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (1633 / 62500) (1633 / 62500) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(60867 / 62500)
  have hx104 : Bounds (1633 / 62500) (1633 / 62500) x104 := by
    exact hx103
  let x105 : ℝ := -(60867 / 62500)
  have hx105 : Bounds (-60867 / 62500) (-60867 / 62500) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((60867 / 62500) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (1633 / 62500) (1633 / 62500) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(60867 / 62500)
  have hx107 : Bounds (1633 / 62500) (1633 / 62500) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-728949549 / 200000000) (-3644747739 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-47614984541 / 500000000000) (-23807492231 / 250000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1246997256819 / 1000000000000) (155874657369 / 125000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (623498628409 / 1000000000000) (155874657369 / 250000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (623498628409 / 1000000000000) (155874657369 / 250000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-155874657369 / 250000000000) (-623498628409 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (17412137631 / 250000000000) (69648552591 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (17412137631 / 250000000000) (69648552591 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (60867 / 62500)
  have hx117 : Bounds (17412137631 / 250000000000) (69648552591 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(48701 / 50000)
  have hx119 : Bounds (98701 / 50000) (98701 / 50000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48701 / 50000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(48701 / 50000)
  have hx120 : Bounds (98701 / 50000) (98701 / 50000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48701 / 50000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (85009009 / 125000000) (680072073 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1342475871569 / 1000000000000) (167809484193 / 125000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(48701 / 50000)
  have hx123 : Bounds (-48701 / 50000) (-48701 / 50000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48701 / 50000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (1299 / 50000) (1299 / 50000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(48701 / 50000)
  have hx125 : Bounds (1299 / 50000) (1299 / 50000) x125 := by
    exact hx124
  let x126 : ℝ := -(48701 / 50000)
  have hx126 : Bounds (-48701 / 50000) (-48701 / 50000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48701 / 50000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (1299 / 50000) (1299 / 50000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(48701 / 50000)
  have hx128 : Bounds (1299 / 50000) (1299 / 50000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-365042827 / 100000000) (-456303533 / 125000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-18967625291 / 200000000000) (-47419063149 / 500000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (623818872557 / 500000000000) (623818873623 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (623818872557 / 1000000000000) (623818873623 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (623818872557 / 1000000000000) (623818873623 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-623818873623 / 1000000000000) (-623818872557 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (69328306377 / 1000000000000) (69328308443 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (69328306377 / 1000000000000) (69328308443 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (48701 / 50000)
  have hx138 : Bounds (69328306377 / 1000000000000) (69328308443 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (60867 / 62500) (48701 / 50000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (48701 / 50000) ≤ (69328308443 / 1000000000000) := hx138.2
      have h2 : (69329075007 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (69647733637 / 1000000000000) := hx96.2
      have h2 : (17412137631 / 250000000000) ≤ biasE (60867 / 62500) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (258033302423 / 250000000000) (64520681903 / 62500000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (71556840711 / 1000000000000) (71899508277 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (71556840711 / 1000000000000) (71899508277 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(194741 / 200000)
  have hx143 : Bounds (394741 / 200000) (394741 / 200000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194741 / 200000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(194741 / 200000)
  have hx144 : Bounds (394741 / 200000) (394741 / 200000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194741 / 200000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (679912487 / 1000000000) (84989061 / 125000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (670973337577 / 500000000000) (1341946677129 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(194741 / 200000)
  have hx147 : Bounds (-194741 / 200000) (-194741 / 200000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194741 / 200000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (5259 / 200000) (5259 / 200000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(194741 / 200000)
  have hx149 : Bounds (5259 / 200000) (5259 / 200000) x149 := by
    exact hx148
  let x150 : ℝ := -(194741 / 200000)
  have hx150 : Bounds (-194741 / 200000) (-194741 / 200000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194741 / 200000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (5259 / 200000) (5259 / 200000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(194741 / 200000)
  have hx152 : Bounds (5259 / 200000) (5259 / 200000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-145535059 / 40000000) (-3638376469 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-95671109411 / 1000000000000) (-23917777313 / 250000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1246275565743 / 1000000000000) (1246275567877 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (623137782871 / 1000000000000) (623137783939 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (623137782871 / 1000000000000) (623137783939 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-623137783939 / 1000000000000) (-623137782871 / 1000000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (70009396061 / 1000000000000) (70009398129 / 1000000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (70009396061 / 1000000000000) (70009398129 / 1000000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (194741 / 200000)
  have hx162 : Bounds (70009396061 / 1000000000000) (70009398129 / 1000000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(194771 / 200000)
  have hx164 : Bounds (394771 / 200000) (394771 / 200000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194771 / 200000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(194771 / 200000)
  have hx165 : Bounds (394771 / 200000) (394771 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194771 / 200000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (679988483 / 1000000000) (169997121 / 250000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1342198667111 / 1000000000000) (671099334543 / 500000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(194771 / 200000)
  have hx168 : Bounds (-194771 / 200000) (-194771 / 200000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194771 / 200000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (5229 / 200000) (5229 / 200000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(194771 / 200000)
  have hx170 : Bounds (5229 / 200000) (5229 / 200000) x170 := by
    exact hx169
  let x171 : ℝ := -(194771 / 200000)
  have hx171 : Bounds (-194771 / 200000) (-194771 / 200000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194771 / 200000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (5229 / 200000) (5229 / 200000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(194771 / 200000)
  have hx173 : Bounds (5229 / 200000) (5229 / 200000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-1822048657 / 500000000) (-911024327 / 250000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-3810996971 / 40000000000) (-95274924117 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (311730935709 / 250000000000) (1246923744969 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (311730935709 / 500000000000) (124692374497 / 200000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (311730935709 / 500000000000) (124692374497 / 200000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-124692374497 / 200000000000) (-311730935709 / 500000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (13937061503 / 200000000000) (34842654791 / 500000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (13937061503 / 200000000000) (34842654791 / 500000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (194771 / 200000)
  have hx183 : Bounds (13937061503 / 200000000000) (34842654791 / 500000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(194741 / 200000)
  have hx184 : Bounds (4354703349 / 62500000000) (70008910707 / 1000000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((194741 / 200000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(194771 / 200000)
  have hx185 : Bounds (6968598711 / 100000000000) (35009847817 / 500000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((194771 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (194741 / 200000) (194771 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (194741 / 200000) ≤ (70008910707 / 1000000000000) := hx184.2
      have h2 : (70009396061 / 1000000000000) ≤ biasE (194741 / 200000) := hx162.1
      linarith
    · have h1 : biasE (194771 / 200000) ≤ (34842654791 / 500000000000) := hx183.2
      have h2 : (6968598711 / 100000000000) ≤ x141 * (194771 / 200000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (123367 / 62500) (98701 / 50000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-48701 / 50000) (-60867 / 62500) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (1299 / 50000) (1633 / 62500) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (1299 / 50000) (1633 / 62500) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (7654623392529 / 200000000000) (19245573518091 / 500000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (7554623392529 / 100000000000) (18995573518091 / 250000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (7554623392529 / 100000000000) (18995573518091 / 250000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (864948967 / 200000000) (541312543 / 125000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (864948967 / 400000000) (541312543 / 250000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (864948967 / 400000000) (541312543 / 250000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (394741 / 200000) (394771 / 200000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-194771 / 200000) (-194741 / 200000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (5229 / 200000) (5259 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (5229 / 200000) (5259 / 200000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (760600874691 / 20000000000) (9562057754829 / 250000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (750600874691 / 10000000000) (9437057754829 / 125000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (750600874691 / 10000000000) (9437057754829 / 125000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (863657791 / 200000000) (2162042899 / 500000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (863657791 / 400000000) (2162042899 / 1000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (863657791 / 400000000) (2162042899 / 1000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (80241962541 / 500000000000) (80626411397 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (69329075007 / 500000000000) (69647733637 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-69647733637 / 500000000000) (-69329075007 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (1324278613 / 62500000000) (1129733639 / 50000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (1324278613 / 62500000000) (1129733639 / 50000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (84234958039 / 40000000000) (527249243133 / 250000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-527249243133 / 250000000000) (-84234958039 / 40000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-521952128681 / 250000000000) (-416655855639 / 200000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-521952128681 / 250000000000) (-416655855639 / 200000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2091523614811 / 1000000000000) (2094732422809 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (3715100087 / 1000000000000) (5726572307 / 500000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (797 / 51200) (3207 / 204800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (797 / 51200) ≤ m → m ≤ (3207 / 204800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3207 / 204800) (1613 / 102400) m) :
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
  have hx0 : Bounds (3207 / 102400) (1613 / 51200) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1613 / 51200) (-3207 / 102400) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (49587 / 51200) (99193 / 102400) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (49587 / 51200) (99193 / 102400) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3207 / 51200) (1613 / 25600) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1613 / 25600) (-3207 / 51200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (23987 / 25600) (47993 / 51200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (23987 / 25600) (47993 / 51200) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(99193 / 102400)
  have hx9 : Bounds (201593 / 102400) (201593 / 102400) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99193 / 102400) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(99193 / 102400)
  have hx10 : Bounds (201593 / 102400) (201593 / 102400) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99193 / 102400) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (6773641 / 10000000) (677364101 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (166689283461 / 125000000000) (666757134829 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(99193 / 102400)
  have hx13 : Bounds (-99193 / 102400) (-99193 / 102400) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99193 / 102400) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3207 / 102400) (3207 / 102400) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(99193 / 102400)
  have hx15 : Bounds (3207 / 102400) (3207 / 102400) x15 := by
    exact hx14
  let x16 : ℝ := -(99193 / 102400)
  have hx16 : Bounds (-99193 / 102400) (-99193 / 102400) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99193 / 102400) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3207 / 102400) (3207 / 102400) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(99193 / 102400)
  have hx18 : Bounds (3207 / 102400) (3207 / 102400) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-1731775397 / 500000000) (-3463550789 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-108472728481 / 1000000000000) (-108472728323 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1225041539207 / 1000000000000) (245008308267 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (612520769603 / 1000000000000) (153130192667 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (612520769603 / 1000000000000) (153130192667 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-153130192667 / 250000000000) (-612520769603 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (20156602333 / 250000000000) (80626411397 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (20156602333 / 250000000000) (80626411397 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (99193 / 102400)
  have hx28 : Bounds (20156602333 / 250000000000) (80626411397 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(49587 / 51200)
  have hx30 : Bounds (100787 / 51200) (100787 / 51200) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49587 / 51200) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(49587 / 51200)
  have hx31 : Bounds (100787 / 51200) (100787 / 51200) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49587 / 51200) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (677269847 / 1000000000) (84658731 / 125000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (666601524117 / 500000000000) (1333203050203 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(49587 / 51200)
  have hx34 : Bounds (-49587 / 51200) (-49587 / 51200) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49587 / 51200) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1613 / 51200) (1613 / 51200) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(49587 / 51200)
  have hx36 : Bounds (1613 / 51200) (1613 / 51200) x36 := by
    exact hx35
  let x37 : ℝ := -(49587 / 51200)
  have hx37 : Bounds (-49587 / 51200) (-49587 / 51200) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49587 / 51200) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1613 / 51200) (1613 / 51200) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(49587 / 51200)
  have hx39 : Bounds (1613 / 51200) (1613 / 51200) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-691528747 / 200000000) (-345764373 / 100000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-54464642037 / 500000000000) (-21785856783 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (3825855513 / 3125000000) (76517110393 / 62500000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (3825855513 / 6250000000) (76517110393 / 125000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (3825855513 / 6250000000) (76517110393 / 125000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-76517110393 / 125000000000) (-3825855513 / 6250000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (10126287107 / 125000000000) (2025257473 / 25000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (10126287107 / 125000000000) (2025257473 / 25000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (49587 / 51200)
  have hx49 : Bounds (10126287107 / 125000000000) (2025257473 / 25000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (20156602333 / 250000000000) (2025257473 / 25000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(47993 / 51200)
  have hx52 : Bounds (99193 / 51200) (99193 / 51200) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((47993 / 51200) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(47993 / 51200)
  have hx53 : Bounds (99193 / 51200) (99193 / 51200) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((47993 / 51200) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (132265583 / 200000000) (165331979 / 250000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (640616209693 / 500000000000) (320308105331 / 250000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(47993 / 51200)
  have hx56 : Bounds (-47993 / 51200) (-47993 / 51200) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((47993 / 51200) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (3207 / 51200) (3207 / 51200) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(47993 / 51200)
  have hx58 : Bounds (3207 / 51200) (3207 / 51200) x58 := by
    exact hx57
  let x59 : ℝ := -(47993 / 51200)
  have hx59 : Bounds (-47993 / 51200) (-47993 / 51200) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((47993 / 51200) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (3207 / 51200) (3207 / 51200) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(47993 / 51200)
  have hx61 : Bounds (3207 / 51200) (3207 / 51200) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2770403613 / 1000000000) (-2770403609 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-43382247983 / 250000000000) (-542278099 / 3125000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (553851713727 / 500000000000) (276925857411 / 250000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (553851713727 / 1000000000000) (276925857411 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (553851713727 / 1000000000000) (276925857411 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-276925857411 / 500000000000) (-553851713727 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (69647732589 / 500000000000) (139295467273 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (69647732589 / 500000000000) (139295467273 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (47993 / 51200)
  have hx71 : Bounds (69647732589 / 500000000000) (139295467273 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(23987 / 25600)
  have hx73 : Bounds (49587 / 25600) (49587 / 25600) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23987 / 25600) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(23987 / 25600)
  have hx74 : Bounds (49587 / 25600) (49587 / 25600) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23987 / 25600) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (661136351 / 1000000000) (20660511 / 31250000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1280615946759 / 1000000000000) (1280615948697 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(23987 / 25600)
  have hx77 : Bounds (-23987 / 25600) (-23987 / 25600) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23987 / 25600) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1613 / 25600) (1613 / 25600) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(23987 / 25600)
  have hx79 : Bounds (1613 / 25600) (1613 / 25600) x79 := by
    exact hx78
  let x80 : ℝ := -(23987 / 25600)
  have hx80 : Bounds (-23987 / 25600) (-23987 / 25600) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23987 / 25600) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1613 / 25600) (1613 / 25600) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(23987 / 25600)
  have hx82 : Bounds (1613 / 25600) (1613 / 25600) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1382248277 / 500000000) (-55289931 / 20000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-43546220133 / 250000000000) (-174184880279 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (1106431066227 / 1000000000000) (553215534209 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (553215533113 / 1000000000000) (553215534209 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (553215533113 / 1000000000000) (553215534209 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-553215534209 / 1000000000000) (-553215533113 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (139931645791 / 1000000000000) (139931647887 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (139931645791 / 1000000000000) (139931647887 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (23987 / 25600)
  have hx92 : Bounds (139931645791 / 1000000000000) (139931647887 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (69647732589 / 500000000000) (139931647887 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (69647732589 / 1000000000000) (8745727993 / 125000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (69647732589 / 1000000000000) (8745727993 / 125000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(38949 / 40000)
  have hx98 : Bounds (78949 / 40000) (78949 / 40000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((38949 / 40000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(38949 / 40000)
  have hx99 : Bounds (78949 / 40000) (78949 / 40000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((38949 / 40000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (33996131 / 50000000) (679922621 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1341980273159 / 1000000000000) (670990137567 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(38949 / 40000)
  have hx102 : Bounds (-38949 / 40000) (-38949 / 40000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((38949 / 40000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (1051 / 40000) (1051 / 40000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(38949 / 40000)
  have hx104 : Bounds (1051 / 40000) (1051 / 40000) x104 := by
    exact hx103
  let x105 : ℝ := -(38949 / 40000)
  have hx105 : Bounds (-38949 / 40000) (-38949 / 40000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((38949 / 40000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (1051 / 40000) (1051 / 40000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(38949 / 40000)
  have hx107 : Bounds (1051 / 40000) (1051 / 40000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-727827473 / 200000000) (-3639137359 / 1000000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-47809167133 / 500000000000) (-95618334107 / 1000000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1246361938893 / 1000000000000) (1246361941027 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (311590484723 / 500000000000) (311590485257 / 500000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (311590484723 / 500000000000) (311590485257 / 500000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-311590485257 / 500000000000) (-311590484723 / 500000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (34983104743 / 500000000000) (34983105777 / 500000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (34983104743 / 500000000000) (34983105777 / 500000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (38949 / 40000)
  have hx117 : Bounds (34983104743 / 500000000000) (34983105777 / 500000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(973873 / 1000000)
  have hx119 : Bounds (1973873 / 1000000) (1973873 / 1000000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((973873 / 1000000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(973873 / 1000000)
  have hx120 : Bounds (1973873 / 1000000) (1973873 / 1000000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((973873 / 1000000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (339998801 / 500000000) (679997603 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (335557226663 / 250000000000) (1342228908627 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(973873 / 1000000)
  have hx123 : Bounds (-973873 / 1000000) (-973873 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((973873 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (26127 / 1000000) (26127 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(973873 / 1000000)
  have hx125 : Bounds (26127 / 1000000) (26127 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := -(973873 / 1000000)
  have hx126 : Bounds (-973873 / 1000000) (-973873 / 1000000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((973873 / 1000000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (26127 / 1000000) (26127 / 1000000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(973873 / 1000000)
  have hx128 : Bounds (26127 / 1000000) (26127 / 1000000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-3644786019 / 1000000000) (-3644786013 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-95227324319 / 1000000000000) (-95227324161 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1247001582333 / 1000000000000) (623500792233 / 500000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (311750395583 / 500000000000) (623500792233 / 1000000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (311750395583 / 500000000000) (623500792233 / 1000000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-623500792233 / 1000000000000) (-311750395583 / 500000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (69646387767 / 1000000000000) (34823194917 / 500000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (69646387767 / 1000000000000) (34823194917 / 500000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (973873 / 1000000)
  have hx138 : Bounds (69646387767 / 1000000000000) (34823194917 / 500000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (38949 / 40000) (973873 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (973873 / 1000000) ≤ (34823194917 / 500000000000) := hx138.2
      have h2 : (69647732589 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (8745727993 / 125000000000) := hx96.2
      have h2 : (34983104743 / 500000000000) ≤ biasE (38949 / 40000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1032330910447 / 1000000000000) (206505737391 / 200000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (35949753597 / 500000000000) (72241720329 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (35949753597 / 500000000000) (72241720329 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(194711 / 200000)
  have hx143 : Bounds (394711 / 200000) (394711 / 200000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194711 / 200000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(194711 / 200000)
  have hx144 : Bounds (394711 / 200000) (394711 / 200000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194711 / 200000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (135967297 / 200000000) (339918243 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (670847347077 / 500000000000) (20963979627 / 15625000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(194711 / 200000)
  have hx147 : Bounds (-194711 / 200000) (-194711 / 200000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194711 / 200000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (5289 / 200000) (5289 / 200000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(194711 / 200000)
  have hx149 : Bounds (5289 / 200000) (5289 / 200000) x149 := by
    exact hx148
  let x150 : ℝ := -(194711 / 200000)
  have hx150 : Bounds (-194711 / 200000) (-194711 / 200000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194711 / 200000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (5289 / 200000) (5289 / 200000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(194711 / 200000)
  have hx152 : Bounds (5289 / 200000) (5289 / 200000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-3632688177 / 1000000000) (-3632688171 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-96066438841 / 1000000000000) (-48033219341 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1245628255313 / 1000000000000) (622814128723 / 500000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (77851765957 / 125000000000) (622814128723 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (77851765957 / 125000000000) (622814128723 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-622814128723 / 1000000000000) (-77851765957 / 125000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (70333051277 / 1000000000000) (2197907917 / 31250000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (70333051277 / 1000000000000) (2197907917 / 31250000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (194711 / 200000)
  have hx162 : Bounds (70333051277 / 1000000000000) (2197907917 / 31250000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(486853 / 500000)
  have hx164 : Bounds (986853 / 500000) (986853 / 500000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((486853 / 500000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(486853 / 500000)
  have hx165 : Bounds (986853 / 500000) (986853 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((486853 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (679912993 / 1000000000) (339956497 / 500000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (670974176881 / 500000000000) (167743544467 / 125000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(486853 / 500000)
  have hx168 : Bounds (-486853 / 500000) (-486853 / 500000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((486853 / 500000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (13147 / 500000) (13147 / 500000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(486853 / 500000)
  have hx170 : Bounds (13147 / 500000) (13147 / 500000) x170 := by
    exact hx169
  let x171 : ℝ := -(486853 / 500000)
  have hx171 : Bounds (-486853 / 500000) (-486853 / 500000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((486853 / 500000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (13147 / 500000) (13147 / 500000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(486853 / 500000)
  have hx173 : Bounds (13147 / 500000) (13147 / 500000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-727682901 / 200000000) (-3638414499 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-19133694199 / 200000000000) (-23917117709 / 250000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1246279882767 / 1000000000000) (12462798849 / 10000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (623139941383 / 1000000000000) (12462798849 / 20000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (623139941383 / 1000000000000) (12462798849 / 20000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-12462798849 / 20000000000) (-623139941383 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (1400144751 / 20000000000) (70007239617 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (1400144751 / 20000000000) (70007239617 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (486853 / 500000)
  have hx183 : Bounds (1400144751 / 20000000000) (70007239617 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(194711 / 200000)
  have hx184 : Bounds (34999062363 / 500000000000) (14066257607 / 200000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((194711 / 200000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(486853 / 500000)
  have hx185 : Bounds (70008981551 / 1000000000000) (14068439307 / 200000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((486853 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (194711 / 200000) (486853 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (194711 / 200000) ≤ (14066257607 / 200000000000) := hx184.2
      have h2 : (70333051277 / 1000000000000) ≤ biasE (194711 / 200000) := hx162.1
      linarith
    · have h1 : biasE (486853 / 500000) ≤ (70007239617 / 1000000000000) := hx183.2
      have h2 : (70008981551 / 1000000000000) ≤ x141 * (486853 / 500000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (78949 / 40000) (1973873 / 1000000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-973873 / 1000000) (-38949 / 40000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (26127 / 1000000) (1051 / 40000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (26127 / 1000000) (1051 / 40000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (19029495718363 / 500000000000) (19137290925097 / 500000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (18779495718363 / 250000000000) (18887290925097 / 250000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (18779495718363 / 250000000000) (18887290925097 / 250000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (4319059979 / 1000000000) (2162391811 / 500000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (4319059979 / 2000000000) (2162391811 / 1000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (4319059979 / 2000000000) (2162391811 / 1000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (394711 / 200000) (986853 / 500000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-486853 / 500000) (-194711 / 200000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (13147 / 500000) (5289 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (13147 / 500000) (5289 / 200000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (4726791453961 / 125000000000) (19015745036891 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (4664291453961 / 62500000000) (18765745036891 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (4664291453961 / 62500000000) (18765745036891 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (269532791 / 62500000) (1727331 / 400000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (269532791 / 125000000) (1727331 / 800000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (269532791 / 125000000) (1727331 / 800000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (20156602333 / 125000000000) (2025257473 / 12500000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (69647732589 / 500000000000) (8745727993 / 62500000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-8745727993 / 62500000000) (-69647732589 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (2665146347 / 125000000000) (11362566331 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (2665146347 / 125000000000) (11362566331 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (84111533561 / 40000000000) (421179000031 / 200000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-421179000031 / 200000000000) (-84111533561 / 40000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2084573829379 / 1000000000000) (-2080063206363 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2084573829379 / 1000000000000) (-2080063206363 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (261041455221 / 125000000000) (2091542283729 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (3757812389 / 1000000000000) (5739538683 / 500000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3207 / 204800) (1613 / 102400) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3207 / 204800) ≤ m → m ≤ (1613 / 102400) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1613 / 102400) (51 / 3200) m) :
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
  have hx0 : Bounds (1613 / 51200) (51 / 1600) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-51 / 1600) (-1613 / 51200) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1549 / 1600) (49587 / 51200) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1549 / 1600) (49587 / 51200) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1613 / 25600) (51 / 800) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-51 / 800) (-1613 / 25600) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (749 / 800) (23987 / 25600) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (749 / 800) (23987 / 25600) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(49587 / 51200)
  have hx9 : Bounds (100787 / 51200) (100787 / 51200) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49587 / 51200) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(49587 / 51200)
  have hx10 : Bounds (100787 / 51200) (100787 / 51200) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((49587 / 51200) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (677269847 / 1000000000) (84658731 / 125000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (666601524117 / 500000000000) (1333203050203 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(49587 / 51200)
  have hx13 : Bounds (-49587 / 51200) (-49587 / 51200) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49587 / 51200) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1613 / 51200) (1613 / 51200) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(49587 / 51200)
  have hx15 : Bounds (1613 / 51200) (1613 / 51200) x15 := by
    exact hx14
  let x16 : ℝ := -(49587 / 51200)
  have hx16 : Bounds (-49587 / 51200) (-49587 / 51200) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((49587 / 51200) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1613 / 51200) (1613 / 51200) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(49587 / 51200)
  have hx18 : Bounds (1613 / 51200) (1613 / 51200) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-691528747 / 200000000) (-345764373 / 100000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-54464642037 / 500000000000) (-21785856783 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (3825855513 / 3125000000) (76517110393 / 62500000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (3825855513 / 6250000000) (76517110393 / 125000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (3825855513 / 6250000000) (76517110393 / 125000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-76517110393 / 125000000000) (-3825855513 / 6250000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (10126287107 / 125000000000) (2025257473 / 25000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (10126287107 / 125000000000) (2025257473 / 25000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (49587 / 51200)
  have hx28 : Bounds (10126287107 / 125000000000) (2025257473 / 25000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1549 / 1600)
  have hx30 : Bounds (3149 / 1600) (3149 / 1600) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1549 / 1600) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1549 / 1600)
  have hx31 : Bounds (3149 / 1600) (3149 / 1600) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1549 / 1600) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (21158791 / 31250000) (677081313 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (66629032859 / 50000000000) (1332580659149 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1549 / 1600)
  have hx34 : Bounds (-1549 / 1600) (-1549 / 1600) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1549 / 1600) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (51 / 1600) (51 / 1600) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1549 / 1600)
  have hx36 : Bounds (51 / 1600) (51 / 1600) x36 := by
    exact hx35
  let x37 : ℝ := -(1549 / 1600)
  have hx37 : Bounds (-1549 / 1600) (-1549 / 1600) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1549 / 1600) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (51 / 1600) (51 / 1600) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1549 / 1600)
  have hx39 : Bounds (51 / 1600) (51 / 1600) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1722966639 / 500000000) (-3445933273 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-109839123237 / 1000000000000) (-27459780769 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (1222741533943 / 1000000000000) (1222741536073 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (611370766971 / 1000000000000) (611370768037 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (611370766971 / 1000000000000) (611370768037 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-611370768037 / 1000000000000) (-611370766971 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (81776411963 / 1000000000000) (81776414029 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (81776411963 / 1000000000000) (81776414029 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1549 / 1600)
  have hx49 : Bounds (81776411963 / 1000000000000) (81776414029 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (10126287107 / 125000000000) (81776414029 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(23987 / 25600)
  have hx52 : Bounds (49587 / 25600) (49587 / 25600) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23987 / 25600) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(23987 / 25600)
  have hx53 : Bounds (49587 / 25600) (49587 / 25600) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23987 / 25600) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (661136351 / 1000000000) (20660511 / 31250000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1280615946759 / 1000000000000) (1280615948697 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(23987 / 25600)
  have hx56 : Bounds (-23987 / 25600) (-23987 / 25600) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23987 / 25600) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1613 / 25600) (1613 / 25600) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(23987 / 25600)
  have hx58 : Bounds (1613 / 25600) (1613 / 25600) x58 := by
    exact hx57
  let x59 : ℝ := -(23987 / 25600)
  have hx59 : Bounds (-23987 / 25600) (-23987 / 25600) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23987 / 25600) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1613 / 25600) (1613 / 25600) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(23987 / 25600)
  have hx61 : Bounds (1613 / 25600) (1613 / 25600) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1382248277 / 500000000) (-55289931 / 20000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-43546220133 / 250000000000) (-174184880279 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1106431066227 / 1000000000000) (553215534209 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (553215533113 / 1000000000000) (553215534209 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (553215533113 / 1000000000000) (553215534209 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-553215534209 / 1000000000000) (-553215533113 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (139931645791 / 1000000000000) (139931647887 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (139931645791 / 1000000000000) (139931647887 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (23987 / 25600)
  have hx71 : Bounds (139931645791 / 1000000000000) (139931647887 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(749 / 800)
  have hx73 : Bounds (1549 / 800) (1549 / 800) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((749 / 800) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(749 / 800)
  have hx74 : Bounds (1549 / 800) (1549 / 800) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((749 / 800) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (82594139 / 125000000) (660753113 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (127938321311 / 100000000000) (1279383215047 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(749 / 800)
  have hx77 : Bounds (-749 / 800) (-749 / 800) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((749 / 800) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (51 / 800) (51 / 800) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(749 / 800)
  have hx79 : Bounds (51 / 800) (51 / 800) x79 := by
    exact hx78
  let x80 : ℝ := -(749 / 800)
  have hx80 : Bounds (-749 / 800) (-749 / 800) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((749 / 800) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (51 / 800) (51 / 800) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(749 / 800)
  have hx82 : Bounds (51 / 800) (51 / 800) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-2752786097 / 1000000000) (-2752786093 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-43872528421 / 250000000000) (-43872528357 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (551946549713 / 500000000000) (1103893101619 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (551946549713 / 1000000000000) (55194655081 / 100000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (551946549713 / 1000000000000) (55194655081 / 100000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-55194655081 / 100000000000) (-551946549713 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (14120062919 / 100000000000) (141200631287 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (14120062919 / 100000000000) (141200631287 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (749 / 800)
  have hx92 : Bounds (14120062919 / 100000000000) (141200631287 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (139931645791 / 1000000000000) (141200631287 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (13993164579 / 200000000000) (17650078911 / 250000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (13993164579 / 200000000000) (17650078911 / 250000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(97343 / 100000)
  have hx98 : Bounds (197343 / 100000) (197343 / 100000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97343 / 100000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(97343 / 100000)
  have hx99 : Bounds (197343 / 100000) (197343 / 100000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97343 / 100000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (135954629 / 200000000) (339886573 / 500000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1341484717537 / 1000000000000) (1341484719511 / 1000000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(97343 / 100000)
  have hx102 : Bounds (-97343 / 100000) (-97343 / 100000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97343 / 100000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (2657 / 100000) (2657 / 100000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(97343 / 100000)
  have hx104 : Bounds (2657 / 100000) (2657 / 100000) x104 := by
    exact hx103
  let x105 : ℝ := -(97343 / 100000)
  have hx105 : Bounds (-97343 / 100000) (-97343 / 100000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97343 / 100000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (2657 / 100000) (2657 / 100000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(97343 / 100000)
  have hx107 : Bounds (2657 / 100000) (2657 / 100000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1813986261 / 500000000) (-906993129 / 250000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-9639522991 / 100000000000) (-385580919 / 4000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1245089487627 / 1000000000000) (1245089489761 / 1000000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (622544743813 / 1000000000000) (622544744881 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (622544743813 / 1000000000000) (622544744881 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-622544744881 / 1000000000000) (-622544743813 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (70602435119 / 1000000000000) (70602437187 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (70602435119 / 1000000000000) (70602437187 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (97343 / 100000)
  have hx117 : Bounds (70602435119 / 1000000000000) (70602437187 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(486863 / 500000)
  have hx119 : Bounds (986863 / 500000) (986863 / 500000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((486863 / 500000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(486863 / 500000)
  have hx120 : Bounds (986863 / 500000) (986863 / 500000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((486863 / 500000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (339961563 / 500000000) (679923127 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1341981951787 / 1000000000000) (670990976881 / 500000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(486863 / 500000)
  have hx123 : Bounds (-486863 / 500000) (-486863 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((486863 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (13137 / 500000) (13137 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(486863 / 500000)
  have hx125 : Bounds (13137 / 500000) (13137 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := -(486863 / 500000)
  have hx126 : Bounds (-486863 / 500000) (-486863 / 500000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((486863 / 500000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (13137 / 500000) (13137 / 500000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(486863 / 500000)
  have hx128 : Bounds (13137 / 500000) (13137 / 500000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-145567017 / 40000000) (-3639175419 / 1000000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-95615695117 / 1000000000000) (-47807847479 / 500000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (124636625667 / 100000000000) (311591564701 / 250000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (124636625667 / 200000000000) (311591564701 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (124636625667 / 200000000000) (311591564701 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-311591564701 / 500000000000) (-124636625667 / 200000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (34982025299 / 500000000000) (13992810533 / 200000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (34982025299 / 500000000000) (13992810533 / 200000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (486863 / 500000)
  have hx138 : Bounds (34982025299 / 500000000000) (13992810533 / 200000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (97343 / 100000) (486863 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (486863 / 500000) ≤ (13992810533 / 200000000000) := hx138.2
      have h2 : (13993164579 / 200000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (17650078911 / 250000000000) := hx96.2
      have h2 : (70602435119 / 1000000000000) ≤ biasE (97343 / 100000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (516264343477 / 500000000000) (1032924467399 / 1000000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (14448343849 / 200000000000) (14584958687 / 200000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (14448343849 / 200000000000) (14584958687 / 200000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(973257 / 1000000)
  have hx143 : Bounds (1973257 / 1000000) (1973257 / 1000000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((973257 / 1000000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(973257 / 1000000)
  have hx144 : Bounds (1973257 / 1000000) (1973257 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((973257 / 1000000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (679685477 / 1000000000) (339842739 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (167649265661 / 125000000000) (670597063631 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(973257 / 1000000)
  have hx147 : Bounds (-973257 / 1000000) (-973257 / 1000000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((973257 / 1000000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (26743 / 1000000) (26743 / 1000000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(973257 / 1000000)
  have hx149 : Bounds (26743 / 1000000) (26743 / 1000000) x149 := by
    exact hx148
  let x150 : ℝ := -(973257 / 1000000)
  have hx150 : Bounds (-973257 / 1000000) (-973257 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((973257 / 1000000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (26743 / 1000000) (26743 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(973257 / 1000000)
  have hx152 : Bounds (26743 / 1000000) (26743 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-144859301 / 40000000) (-3621482519 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-96849307167 / 1000000000000) (-19369861401 / 200000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (1244344818121 / 1000000000000) (1244344820257 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (31108620453 / 50000000000) (622172410129 / 1000000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (31108620453 / 50000000000) (622172410129 / 1000000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-622172410129 / 1000000000000) (-31108620453 / 50000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (70974769871 / 1000000000000) (3548738597 / 50000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (70974769871 / 1000000000000) (3548738597 / 50000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (973257 / 1000000)
  have hx162 : Bounds (70974769871 / 1000000000000) (3548738597 / 50000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(243389 / 250000)
  have hx164 : Bounds (493389 / 250000) (493389 / 250000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243389 / 250000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(243389 / 250000)
  have hx165 : Bounds (493389 / 250000) (493389 / 250000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243389 / 250000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (679836991 / 1000000000) (10622453 / 15625000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (1341696372609 / 1000000000000) (167712046823 / 125000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(243389 / 250000)
  have hx168 : Bounds (-243389 / 250000) (-243389 / 250000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243389 / 250000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (6611 / 250000) (6611 / 250000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(243389 / 250000)
  have hx170 : Bounds (6611 / 250000) (6611 / 250000) x170 := by
    exact hx169
  let x171 : ℝ := -(243389 / 250000)
  have hx171 : Bounds (-243389 / 250000) (-243389 / 250000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243389 / 250000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (6611 / 250000) (6611 / 250000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(243389 / 250000)
  have hx173 : Bounds (6611 / 250000) (6611 / 250000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-454090749 / 125000000) (-1816362993 / 500000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-96063806133 / 1000000000000) (-96063805973 / 1000000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (311408141619 / 250000000000) (1245632568611 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (311408141619 / 500000000000) (311408142153 / 500000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (311408141619 / 500000000000) (311408142153 / 500000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-311408142153 / 500000000000) (-311408141619 / 500000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (35165447847 / 500000000000) (35165448881 / 500000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (35165447847 / 500000000000) (35165448881 / 500000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (243389 / 250000)
  have hx183 : Bounds (35165447847 / 500000000000) (35165448881 / 500000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(973257 / 1000000)
  have hx184 : Bounds (70309758947 / 1000000000000) (14194913137 / 200000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((973257 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(243389 / 250000)
  have hx185 : Bounds (70331359221 / 1000000000000) (35498185099 / 500000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((243389 / 250000) : ℝ)) <;> norm_num
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
  have hc : Bounds (973257 / 1000000) (243389 / 250000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (973257 / 1000000) ≤ (14194913137 / 200000000000) := hx184.2
      have h2 : (70974769871 / 1000000000000) ≤ biasE (973257 / 1000000) := hx162.1
      linarith
    · have h1 : biasE (243389 / 250000) ≤ (35165448881 / 500000000000) := hx183.2
      have h2 : (70331359221 / 1000000000000) ≤ x141 * (243389 / 250000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (197343 / 100000) (986863 / 500000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-486863 / 500000) (-97343 / 100000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (13137 / 500000) (2657 / 100000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (13137 / 500000) (2657 / 100000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (117613850207 / 3125000000) (38060439978687 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (116051350207 / 1562500000) (37560439978687 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (116051350207 / 1562500000) (37560439978687 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (4307745661 / 1000000000) (539887319 / 125000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (4307745661 / 2000000000) (539887319 / 250000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (4307745661 / 2000000000) (539887319 / 250000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (1973257 / 1000000) (493389 / 250000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-243389 / 250000) (-973257 / 1000000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (6611 / 250000) (26743 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (6611 / 250000) (26743 / 1000000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (3739296264443 / 100000000000) (37815761609439 / 1000000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (3689296264443 / 50000000000) (37315761609439 / 500000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (3689296264443 / 50000000000) (37315761609439 / 500000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (860233599 / 200000000) (539070373 / 125000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (860233599 / 400000000) (539070373 / 250000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (860233599 / 400000000) (539070373 / 250000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (10126287107 / 62500000000) (81776414029 / 500000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (13993164579 / 100000000000) (17650078911 / 125000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-17650078911 / 125000000000) (-13993164579 / 100000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (2602495303 / 125000000000) (5905295567 / 250000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (2602495303 / 125000000000) (5905295567 / 250000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (2096644429393 / 1000000000000) (2102809278323 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-2102809278323 / 1000000000000) (-2096644429393 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-2081989315899 / 1000000000000) (-16584185977 / 8000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-2081989315899 / 1000000000000) (-16584185977 / 8000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (2082034132579 / 1000000000000) (522087550507 / 250000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (1120417 / 25000000000) (15326954903 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1613 / 102400) (51 / 3200) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1613 / 102400) ≤ m → m ≤ (51 / 3200) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069

end


