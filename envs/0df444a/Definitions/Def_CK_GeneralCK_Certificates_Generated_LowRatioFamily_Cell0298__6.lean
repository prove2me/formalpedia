-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0298__6
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0298__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:18:01.062904+00:00
-- url     : https://prove2.me/theorems/f9f3e02d-ee9f-41bf-923f-1eb2684b3c46
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0298 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0299, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0298 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0299, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0300, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0301, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0302, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0303)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0298 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0299, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0300, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0301, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0302, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0303)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0298 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0299, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0300, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0301, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0302, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0303) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0298 (+5 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0299, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0300, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0301, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0302, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0303).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0062__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0065__2

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0298 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_298 (a z s c : ℝ)
    (ha : Bounds (899 / 5000) (1799 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (898101 / 10000000) (1800799 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (444522485559754660686963923 / 1170486277712802000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1799 / 10000)
  have hx1 : Bounds (11799 / 10000) (11799 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1799 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1799 / 10000)
  have hx2 : Bounds (11799 / 10000) (11799 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1799 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (165429689 / 1000000000) (16542969 / 100000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4143.1) (by simpa only [div_one] using reflection_log_4143.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (195190490051 / 1000000000000) (195190491231 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1799 / 10000)
  have hx5 : Bounds (-1799 / 10000) (-1799 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1799 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8201 / 10000) (8201 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1799 / 10000)
  have hx7 : Bounds (8201 / 10000) (8201 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1799 / 10000)
  have hx8 : Bounds (-1799 / 10000) (-1799 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1799 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8201 / 10000) (8201 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1799 / 10000)
  have hx10 : Bounds (8201 / 10000) (8201 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-39665799 / 200000000) (-99164497 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4144.1) (by simpa only [div_one] using reflection_log_4144.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-203312011 / 1250000000) (-162649607979 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (32540881251 / 1000000000000) (8135220813 / 250000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (5206541 / 320000000) (8135220813 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (5206541 / 320000000) (8135220813 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-8135220813 / 500000000000) (-5206541 / 320000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (338438369187 / 500000000000) (5415013923 / 8000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (338438369187 / 500000000000) (5415013923 / 8000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1799 / 10000)
  have hx20 : Bounds (338438369187 / 500000000000) (5415013923 / 8000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(899 / 5000)
  have hx22 : Bounds (5899 / 5000) (5899 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((899 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(899 / 5000)
  have hx23 : Bounds (5899 / 5000) (5899 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((899 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (41336233 / 250000000) (165344933 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4129.1) (by simpa only [div_one] using reflection_log_4129.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (195073950773 / 1000000000000) (97536975977 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(899 / 5000)
  have hx26 : Bounds (-899 / 5000) (-899 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((899 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4101 / 5000) (4101 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(899 / 5000)
  have hx28 : Bounds (4101 / 5000) (4101 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(899 / 5000)
  have hx29 : Bounds (-899 / 5000) (-899 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((899 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4101 / 5000) (4101 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(899 / 5000)
  have hx31 : Bounds (4101 / 5000) (4101 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-198207067 / 1000000000) (-99103533 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4130.1) (by simpa only [div_one] using reflection_log_4130.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-81284718177 / 500000000000) (-162569435533 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (32504514419 / 1000000000000) (32504516421 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (16252257209 / 1000000000000) (16252258211 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (16252257209 / 1000000000000) (16252258211 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-16252258211 / 1000000000000) (-16252257209 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (676894921789 / 1000000000000) (676894923791 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (676894921789 / 1000000000000) (676894923791 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (899 / 5000)
  have hx41 : Bounds (676894921789 / 1000000000000) (676894923791 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (338438369187 / 500000000000) (676894923791 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1799 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1799 / 10000000)
  have hx45 : Bounds (10001799 / 10000000) (10001799 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1799 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1799 / 10000000)
  have hx46 : Bounds (10001799 / 10000000) (10001799 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1799 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (179883 / 1000000000) (44971 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4145.1) (by simpa only [div_one] using reflection_log_4145.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (1124471 / 6250000000) (89958181 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1799 / 10000000)
  have hx49 : Bounds (-1799 / 10000000) (-1799 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1799 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998201 / 10000000) (9998201 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1799 / 10000000)
  have hx51 : Bounds (9998201 / 10000000) (9998201 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1799 / 10000000)
  have hx52 : Bounds (-1799 / 10000000) (-1799 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1799 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998201 / 10000000) (9998201 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1799 / 10000000)
  have hx54 : Bounds (9998201 / 10000000) (9998201 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-179917 / 1000000000) (-44979 / 250000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4146.1) (by simpa only [div_one] using reflection_log_4146.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-179884633 / 1000000000000) (-179883633 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (30727 / 1000000000000) (32729 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (15363 / 1000000000000) (3273 / 200000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (15363 / 1000000000000) (3273 / 200000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-3273 / 200000000000) (-15363 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (138629432727 / 200000000000) (693147165637 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (138629432727 / 200000000000) (693147165637 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1799 / 10000000)
  have hx64 : Bounds (138629432727 / 200000000000) (693147165637 / 1000000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(0 / 1)
  have hx66 : Bounds (1 / 1) (1 / 1) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(0 / 1)
  have hx67 : Bounds (1 / 1) (1 / 1) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (0 / 1) (0 / 1) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (0 / 1) (0 / 1) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(0 / 1)
  have hx70 : Bounds (0 / 1) (0 / 1) x70 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1 / 1) (1 / 1) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(0 / 1)
  have hx72 : Bounds (1 / 1) (1 / 1) x72 := by
    exact hx71
  let x73 : ℝ := -(0 / 1)
  have hx73 : Bounds (0 / 1) (0 / 1) x73 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(0 / 1)
  have hx75 : Bounds (1 / 1) (1 / 1) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (0 / 1) (0 / 1) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (0 / 1) (0 / 1) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (0 / 1) (0 / 1) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (0 / 1)
  have hx85 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (138629432727 / 200000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1370023902009 / 1000000000000) (1370042104791 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (171252987751 / 250000000000) (171255263099 / 250000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (171252987751 / 250000000000) (171255263099 / 250000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (5553090600339 / 500000000000) (2783651281983 / 250000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (11887291957 / 1562500000) (30509755691 / 4000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (11887291957 / 1562500000) (30509755691 / 4000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(90339 / 1000000)
  have hx95 : Bounds (1090339 / 1000000) (1090339 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90339 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(90339 / 1000000)
  have hx96 : Bounds (1090339 / 1000000) (1090339 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90339 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (86488657 / 1000000000) (43244329 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4147.1) (by simpa only [div_one] using reflection_log_4147.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (11787744473 / 125000000000) (23575489219 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(90339 / 1000000)
  have hx99 : Bounds (-90339 / 1000000) (-90339 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90339 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (909661 / 1000000) (909661 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(90339 / 1000000)
  have hx101 : Bounds (909661 / 1000000) (909661 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(90339 / 1000000)
  have hx102 : Bounds (-90339 / 1000000) (-90339 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90339 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (909661 / 1000000) (909661 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(90339 / 1000000)
  have hx104 : Bounds (909661 / 1000000) (909661 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-94683277 / 1000000000) (-23670819 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4148.1) (by simpa only [div_one] using reflection_log_4148.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-2153242111 / 25000000000) (-86129683529 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (510766959 / 62500000000) (8172273347 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (510766959 / 125000000000) (2043068337 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (510766959 / 125000000000) (2043068337 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2043068337 / 500000000000) (-510766959 / 125000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (344530521663 / 500000000000) (43066315333 / 62500000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (344530521663 / 500000000000) (43066315333 / 62500000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (90339 / 1000000)
  have hx114 : Bounds (344530521663 / 500000000000) (43066315333 / 62500000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(9057 / 100000)
  have hx116 : Bounds (109057 / 100000) (109057 / 100000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9057 / 100000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(9057 / 100000)
  have hx117 : Bounds (109057 / 100000) (109057 / 100000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9057 / 100000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (17340099 / 200000000) (5418781 / 62500000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4149.1) (by simpa only [div_one] using reflection_log_4149.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (5909559927 / 62500000000) (94552959923 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(9057 / 100000)
  have hx120 : Bounds (-9057 / 100000) (-9057 / 100000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9057 / 100000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (90943 / 100000) (90943 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(9057 / 100000)
  have hx122 : Bounds (90943 / 100000) (90943 / 100000) x122 := by
    exact hx121
  let x123 : ℝ := -(9057 / 100000)
  have hx123 : Bounds (-9057 / 100000) (-9057 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9057 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (90943 / 100000) (90943 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(9057 / 100000)
  have hx125 : Bounds (90943 / 100000) (90943 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-379749 / 4000000) (-94937249 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4150.1) (by simpa only [div_one] using reflection_log_4150.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-21584695817 / 250000000000) (-43169391179 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (2053543891 / 250000000000) (1642835513 / 200000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2053543891 / 500000000000) (4107088783 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2053543891 / 500000000000) (4107088783 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4107088783 / 1000000000000) (-2053543891 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (689040091217 / 1000000000000) (344520046609 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (689040091217 / 1000000000000) (344520046609 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (9057 / 100000)
  have hx135 : Bounds (689040091217 / 1000000000000) (344520046609 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(90339 / 1000000)
  have hx136 : Bounds (343643541793 / 500000000000) (689055204843 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((90339 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(9057 / 100000)
  have hx137 : Bounds (689044500829 / 1000000000000) (345408571617 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((9057 / 100000) : ℝ)) <;> norm_num
  have hc : Bounds (90339 / 1000000) (9057 / 100000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(90339 / 1000000) ≤ (689055204843 / 1000000000000) := hx136.2
      have h2 : (344530521663 / 500000000000) ≤ biasE (90339 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (9057 / 100000) ≤ (344520046609 / 500000000000) := hx135.2
      have h2 : (689044500829 / 1000000000000) ≤ x93*(9057 / 100000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(9057 / 100000)
  have hx139 : Bounds (109057 / 100000) (109057 / 100000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9057 / 100000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(9057 / 100000)
  have hx140 : Bounds (109057 / 100000) (109057 / 100000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9057 / 100000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (17340099 / 200000000) (5418781 / 62500000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4149.1) (by simpa only [div_one] using reflection_log_4149.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (5909559927 / 62500000000) (94552959923 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(9057 / 100000)
  have hx143 : Bounds (-9057 / 100000) (-9057 / 100000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9057 / 100000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (90943 / 100000) (90943 / 100000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(9057 / 100000)
  have hx145 : Bounds (90943 / 100000) (90943 / 100000) x145 := by
    exact hx144
  let x146 : ℝ := -(9057 / 100000)
  have hx146 : Bounds (-9057 / 100000) (-9057 / 100000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9057 / 100000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (90943 / 100000) (90943 / 100000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(9057 / 100000)
  have hx148 : Bounds (90943 / 100000) (90943 / 100000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-379749 / 4000000) (-94937249 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4150.1) (by simpa only [div_one] using reflection_log_4150.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-21584695817 / 250000000000) (-43169391179 / 500000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (2053543891 / 250000000000) (1642835513 / 200000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (2053543891 / 500000000000) (4107088783 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (2053543891 / 500000000000) (4107088783 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4107088783 / 1000000000000) (-2053543891 / 500000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (689040091217 / 1000000000000) (344520046609 / 500000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (689040091217 / 1000000000000) (344520046609 / 500000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (9057 / 100000)
  have hx158 : Bounds (689040091217 / 1000000000000) (344520046609 / 500000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(90339 / 1000000)
  have hx160 : Bounds (1090339 / 1000000) (1090339 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90339 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(90339 / 1000000)
  have hx161 : Bounds (1090339 / 1000000) (1090339 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90339 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (86488657 / 1000000000) (43244329 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4147.1) (by simpa only [div_one] using reflection_log_4147.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (11787744473 / 125000000000) (23575489219 / 250000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(90339 / 1000000)
  have hx164 : Bounds (-90339 / 1000000) (-90339 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90339 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (909661 / 1000000) (909661 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(90339 / 1000000)
  have hx166 : Bounds (909661 / 1000000) (909661 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(90339 / 1000000)
  have hx167 : Bounds (-90339 / 1000000) (-90339 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90339 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (909661 / 1000000) (909661 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(90339 / 1000000)
  have hx169 : Bounds (909661 / 1000000) (909661 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-94683277 / 1000000000) (-23670819 / 250000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4148.1) (by simpa only [div_one] using reflection_log_4148.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-2153242111 / 25000000000) (-86129683529 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (510766959 / 62500000000) (8172273347 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (510766959 / 125000000000) (2043068337 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (510766959 / 125000000000) (2043068337 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-2043068337 / 500000000000) (-510766959 / 125000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (344530521663 / 500000000000) (43066315333 / 62500000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (344530521663 / 500000000000) (43066315333 / 62500000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (90339 / 1000000)
  have hx179 : Bounds (344530521663 / 500000000000) (43066315333 / 62500000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (689040091217 / 1000000000000) (43066315333 / 62500000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-82029249 / 10000000000) (-8161134921 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-1647351 / 200000000) (-8194619 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4151.1) (by simpa only [div_one] using reflection_log_4152.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-1647351 / 400000000) (-8194619 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-1647351 / 400000000) (-8194619 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (8194619 / 2000000000) (1647351 / 400000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1394488979 / 2000000000) (1394531117 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1394488979 / 2000000000) (1394531117 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (90339 / 1000000) (9057 / 100000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-82029249 / 10000000000) (-8161134921 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1090339 / 1000000) (109057 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-9057 / 100000) (-90339 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (90943 / 100000) (909661 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (90943 / 100000) (909661 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (274827655577 / 250000000000) (219917970597 / 200000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (149827655577 / 125000000000) (119917970597 / 100000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (149827655577 / 125000000000) (119917970597 / 100000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (181171933 / 1000000000) (36327549 / 200000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4153.1) (by simpa only [div_one] using reflection_log_4154.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (181171933 / 2000000000) (36327549 / 400000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (181171933 / 2000000000) (36327549 / 400000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (5899 / 5000) (11799 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1799 / 10000) (-899 / 5000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8201 / 10000) (4101 / 5000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8201 / 10000) (4101 / 5000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (304803706413 / 250000000000) (609681746129 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (179803706413 / 125000000000) (359681746129 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (179803706413 / 125000000000) (359681746129 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (181775999 / 500000000) (72751737 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4155.1) (by simpa only [div_one] using reflection_log_4156.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (181775999 / 1000000000) (72751737 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (181775999 / 1000000000) (72751737 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1394488979 / 1000000000) (1394531117 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (90339 / 1000000) (9057 / 100000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-82029249 / 10000000000) (-8161134921 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (13862860541 / 10000000000) (1386369982079 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (13862860541 / 10000000000) (1386369982079 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (955206669169 / 1000000000000) (955293549063 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (171252987751 / 125000000000) (171255263099 / 125000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (30739419943 / 31250000000) (491872167141 / 500000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (30739419943 / 31250000000) (491872167141 / 500000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (168454960223 / 125000000000) (1347771158317 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1394488979 / 2000000000) (1394531117 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (243074939069 / 500000000000) (486179259071 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169482661801 / 500000000000) (2648406661 / 7812500000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169482661801 / 500000000000) (2648406661 / 7812500000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (228401560417 / 500000000000) (456889102489 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2188714930061 / 1000000000000) (2189126900391 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (261334387263 / 125000000000) (261407350753 / 125000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (261334387263 / 125000000000) (261407350753 / 125000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-36327549 / 400000000) (-181171933 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1394488979 / 1000000000) (1394531117 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (90339 / 1000000) (9057 / 100000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-82029249 / 10000000000) (-8161134921 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (13862860541 / 10000000000) (1386369982079 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (13862860541 / 10000000000) (1386369982079 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-125908558641 / 1000000000000) (-15697257757 / 125000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (504114143541 / 500000000000) (1008270769401 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (45541167613 / 500000000000) (18263816717 / 200000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (45541167613 / 500000000000) (18263816717 / 200000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (45541167613 / 250000000000) (18263816717 / 100000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (90339 / 500000) (9057 / 50000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-9057 / 50000) (-90339 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (256167613 / 250000000000) (196016717 / 100000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (256167613 / 250000000000) (196016717 / 100000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (706039021 / 1000000000000) (33766871 / 25000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-6260125981 / 50000000000) (-7764211701 / 62500000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (171252987751 / 125000000000) (171255263099 / 125000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (30739419943 / 31250000000) (491872167141 / 500000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (30739419943 / 31250000000) (491872167141 / 500000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (168454960223 / 125000000000) (1347771158317 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1394488979 / 2000000000) (1394531117 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (243074939069 / 500000000000) (486179259071 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169482661801 / 500000000000) (2648406661 / 7812500000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169482661801 / 500000000000) (2648406661 / 7812500000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (228401560417 / 500000000000) (456889102489 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2188714930061 / 1000000000000) (2189126900391 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-274084203697 / 1000000000000) (-135949168561 / 500000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-274084203697 / 1000000000000) (-135949168561 / 500000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (90339 / 250000) (9057 / 25000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (504114143541 / 500000000000) (1008270769401 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (182164670453 / 500000000000) (365276334339 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (182164670453 / 500000000000) (365276334339 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (271017 / 1000000) (27171 / 100000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (138305009063 / 200000000000) (345787540101 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (28919492001 / 20000000000) (1446079222691 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (391883698181 / 1000000000000) (196457092799 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (391883698181 / 1000000000000) (196457092799 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-196457092799 / 500000000000) (-391883698181 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-7146211173 / 250000000000) (-13303681921 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-7146211173 / 250000000000) (-13303681921 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-59778308181 / 1000000000000) (-5562735301 / 100000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-166931255939 / 500000000000) (-81881422533 / 250000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1394488979 / 1000000000) (1394531117 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (90339 / 1000000) (9057 / 100000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (8161134921 / 1000000000000) (82029249 / 10000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-82029249 / 10000000000) (-8161134921 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (13862860541 / 10000000000) (1386369982079 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (13862860541 / 10000000000) (1386369982079 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (125235695841 / 1000000000000) (125563529277 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (9917970751 / 10000000000) (991838865079 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (30739419943 / 31250000000) (491872167141 / 500000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (30739419943 / 31250000000) (491872167141 / 500000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1394488979 / 2000000000) (1394531117 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (243074939069 / 500000000000) (486179259071 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (243074939069 / 500000000000) (486179259071 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (239103444149 / 500000000000) (478276091557 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (522710635997 / 250000000000) (2091145118297 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (26184812089 / 100000000000) (65642890321 / 250000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (26184812089 / 100000000000) (65642890321 / 250000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (16421461973 / 1000000000000) (16472812051 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (70546155319 / 100000000000) (705533857379 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (70546155319 / 100000000000) (705533857379 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (497676003029 / 1000000000000) (497778023909 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (497676003029 / 1000000000000) (497778023909 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-8309471071 / 50000000000) (-81500838177 / 500000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (261334387263 / 62500000000) (261407350753 / 62500000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (16421461973 / 1000000000000) (16472812051 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (70546155319 / 100000000000) (705533857379 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (368722725481 / 125000000000) (46107934131 / 15625000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-36327549 / 400000000) (-181171933 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (181914253 / 2000000000) (1426459 / 15625000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (181914253 / 2000000000) (1426459 / 15625000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (6707591917 / 25000000000) (134699166951 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (5105712763 / 50000000000) (26599164387 / 250000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (899 / 5000) (1799 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (808201 / 25000000) (3236401 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (808201 / 25000000) (3236401 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3236401 / 100000000) (-808201 / 25000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96763599 / 100000000) (24191799 / 25000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96763599 / 100000000) (24191799 / 25000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1033408057003 / 1000000000000) (1033446471953 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1033408057003 / 1000000000000) (1033446471953 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1033408057003 / 1000000000000) (1033446471953 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (135297978919 / 500000000000) (54270730729 / 200000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (186355106549 / 500000000000) (377750311193 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (689040091217 / 1000000000000) (43066315333 / 62500000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (59347030913 / 125000000000) (474805124189 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (59347030913 / 125000000000) (474805124189 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (88476978153 / 500000000000) (179357783419 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477620808079 / 1000000000000) (119410396671 / 250000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (1046810022283 / 500000000000) (2093711126243 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (370474349887 / 1000000000000) (375523386723 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (370474349887 / 1000000000000) (375523386723 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (444522485559754660686963923 / 1170486277712802000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_298 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((899 / 5000):ℝ) ((1799 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (444522485559754660686963923 / 1170486277712802000000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (898101 / 10000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1800799 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1799 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_298 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_298 {a z : ℝ}
    (ha : a ∈ Set.Icc ((899 / 5000):ℝ) ((1799 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_298 ha ⟨hz.1.le,hz.2⟩ hs) (M := (444522485559754660686963923 / 1170486277712802000000000000))
  exact lt_of_lt_of_le (by norm_num : (444522485559754660686963923 / 1170486277712802000000000000) < 2*((899 / 5000):ℝ)/(1-((899 / 5000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0299 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_299 (a z s c : ℝ)
    (ha : Bounds (1799 / 10000) (9 / 50) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1797201 / 20000000) (9009 / 100000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (711618471085944139641354787 / 1872638818286560200000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(9 / 50)
  have hx1 : Bounds (59 / 50) (59 / 50) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 50) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(9 / 50)
  have hx2 : Bounds (59 / 50) (59 / 50) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 50) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (82757219 / 500000000) (165514439 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4157.1) (by simpa only [div_one] using reflection_log_4157.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (4882675921 / 25000000000) (9765351901 / 50000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(9 / 50)
  have hx5 : Bounds (-9 / 50) (-9 / 50) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 50) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (41 / 50) (41 / 50) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(9 / 50)
  have hx7 : Bounds (41 / 50) (41 / 50) x7 := by
    exact hx6
  let x8 : ℝ := -(9 / 50)
  have hx8 : Bounds (-9 / 50) (-9 / 50) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 50) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (41 / 50) (41 / 50) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(9 / 50)
  have hx10 : Bounds (41 / 50) (41 / 50) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-198450939 / 1000000000) (-99225469 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4158.1) (by simpa only [div_one] using reflection_log_4158.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-8136488499 / 50000000000) (-4068244229 / 25000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (1628863343 / 50000000000) (1628863443 / 50000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (1628863343 / 100000000000) (1628863443 / 100000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (1628863343 / 100000000000) (1628863443 / 100000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-1628863443 / 100000000000) (-1628863343 / 100000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (67685854557 / 100000000000) (67685854757 / 100000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (67685854557 / 100000000000) (67685854757 / 100000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (9 / 50)
  have hx20 : Bounds (67685854557 / 100000000000) (67685854757 / 100000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1799 / 10000)
  have hx22 : Bounds (11799 / 10000) (11799 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1799 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1799 / 10000)
  have hx23 : Bounds (11799 / 10000) (11799 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1799 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (165429689 / 1000000000) (16542969 / 100000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4143.1) (by simpa only [div_one] using reflection_log_4143.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (195190490051 / 1000000000000) (195190491231 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1799 / 10000)
  have hx26 : Bounds (-1799 / 10000) (-1799 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1799 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8201 / 10000) (8201 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1799 / 10000)
  have hx28 : Bounds (8201 / 10000) (8201 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1799 / 10000)
  have hx29 : Bounds (-1799 / 10000) (-1799 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1799 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8201 / 10000) (8201 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1799 / 10000)
  have hx31 : Bounds (8201 / 10000) (8201 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-39665799 / 200000000) (-99164497 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4144.1) (by simpa only [div_one] using reflection_log_4144.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-203312011 / 1250000000) (-162649607979 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (32540881251 / 1000000000000) (8135220813 / 250000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (5206541 / 320000000) (8135220813 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (5206541 / 320000000) (8135220813 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-8135220813 / 500000000000) (-5206541 / 320000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (338438369187 / 500000000000) (5415013923 / 8000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (338438369187 / 500000000000) (5415013923 / 8000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1799 / 10000)
  have hx41 : Bounds (338438369187 / 500000000000) (5415013923 / 8000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (67685854557 / 100000000000) (5415013923 / 8000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (9 / 50000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(9 / 50000)
  have hx45 : Bounds (50009 / 50000) (50009 / 50000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 50000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(9 / 50000)
  have hx46 : Bounds (50009 / 50000) (50009 / 50000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 50000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (179983 / 1000000000) (11249 / 62500000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4159.1) (by simpa only [div_one] using reflection_log_4159.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (45003849 / 250000000000) (90008199 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(9 / 50000)
  have hx49 : Bounds (-9 / 50000) (-9 / 50000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 50000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (49991 / 50000) (49991 / 50000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(9 / 50000)
  have hx51 : Bounds (49991 / 50000) (49991 / 50000) x51 := by
    exact hx50
  let x52 : ℝ := -(9 / 50000)
  have hx52 : Bounds (-9 / 50000) (-9 / 50000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 50000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (49991 / 50000) (49991 / 50000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(9 / 50000)
  have hx54 : Bounds (49991 / 50000) (49991 / 50000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-180017 / 1000000000) (-11251 / 62500000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4160.1) (by simpa only [div_one] using reflection_log_4160.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-179984597 / 1000000000000) (-179983597 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (30799 / 1000000000000) (32801 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (15399 / 1000000000000) (16401 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (15399 / 1000000000000) (16401 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-16401 / 1000000000000) (-15399 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147163599 / 1000000000000) (693147165601 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147163599 / 1000000000000) (693147165601 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (9 / 50000)
  have hx64 : Bounds (693147163599 / 1000000000000) (693147165601 / 1000000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(0 / 1)
  have hx66 : Bounds (1 / 1) (1 / 1) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(0 / 1)
  have hx67 : Bounds (1 / 1) (1 / 1) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (0 / 1) (0 / 1) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (0 / 1) (0 / 1) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(0 / 1)
  have hx70 : Bounds (0 / 1) (0 / 1) x70 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1 / 1) (1 / 1) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(0 / 1)
  have hx72 : Bounds (1 / 1) (1 / 1) x72 := by
    exact hx71
  let x73 : ℝ := -(0 / 1)
  have hx73 : Bounds (0 / 1) (0 / 1) x73 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(0 / 1)
  have hx75 : Bounds (1 / 1) (1 / 1) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (0 / 1) (0 / 1) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (0 / 1) (0 / 1) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (0 / 1) (0 / 1) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (0 / 1)
  have hx85 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (693147163599 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1370005709169 / 1000000000000) (10960191371 / 8000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (85625356823 / 125000000000) (42813247543 / 62500000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (85625356823 / 125000000000) (42813247543 / 62500000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (11100011100011 / 1000000000000) (11128415797677 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7603539289421 / 1000000000000) (7623097924919 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7603539289421 / 1000000000000) (7623097924919 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(9039 / 100000)
  have hx95 : Bounds (109039 / 100000) (109039 / 100000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9039 / 100000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(9039 / 100000)
  have hx96 : Bounds (109039 / 100000) (109039 / 100000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9039 / 100000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (8653543 / 100000000) (86535431 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4161.1) (by simpa only [div_one] using reflection_log_4161.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (94357367517 / 1000000000000) (94357368609 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(9039 / 100000)
  have hx99 : Bounds (-9039 / 100000) (-9039 / 100000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9039 / 100000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (90961 / 100000) (90961 / 100000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(9039 / 100000)
  have hx101 : Bounds (90961 / 100000) (90961 / 100000) x101 := by
    exact hx100
  let x102 : ℝ := -(9039 / 100000)
  have hx102 : Bounds (-9039 / 100000) (-9039 / 100000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9039 / 100000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (90961 / 100000) (90961 / 100000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(9039 / 100000)
  have hx104 : Bounds (90961 / 100000) (90961 / 100000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-94739343 / 1000000000) (-47369671 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4162.1) (by simpa only [div_one] using reflection_log_4162.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-86175853787 / 1000000000000) (-21543963219 / 250000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (818151373 / 100000000000) (8181515733 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (818151373 / 200000000000) (4090757867 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (818151373 / 200000000000) (4090757867 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4090757867 / 1000000000000) (-818151373 / 200000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (689056422133 / 1000000000000) (137811284827 / 200000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (689056422133 / 1000000000000) (137811284827 / 200000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (9039 / 100000)
  have hx114 : Bounds (689056422133 / 1000000000000) (137811284827 / 200000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(90621 / 1000000)
  have hx116 : Bounds (1090621 / 1000000) (1090621 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90621 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(90621 / 1000000)
  have hx117 : Bounds (1090621 / 1000000) (1090621 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90621 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (43373629 / 500000000) (86747259 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4163.1) (by simpa only [div_one] using reflection_log_4163.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (94608381267 / 1000000000000) (47304191179 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(90621 / 1000000)
  have hx120 : Bounds (-90621 / 1000000) (-90621 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90621 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (909379 / 1000000) (909379 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(90621 / 1000000)
  have hx122 : Bounds (909379 / 1000000) (909379 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(90621 / 1000000)
  have hx123 : Bounds (-90621 / 1000000) (-90621 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90621 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (909379 / 1000000) (909379 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(90621 / 1000000)
  have hx125 : Bounds (909379 / 1000000) (909379 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-94993331 / 1000000000) (-9499333 / 100000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4164.1) (by simpa only [div_one] using reflection_log_4164.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-1349764693 / 15625000000) (-43192469721 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (1644688183 / 200000000000) (2055860729 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4111720457 / 1000000000000) (2055860729 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4111720457 / 1000000000000) (2055860729 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2055860729 / 500000000000) (-4111720457 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (344517729271 / 500000000000) (689035460543 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (344517729271 / 500000000000) (689035460543 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (90621 / 1000000)
  have hx135 : Bounds (344517729271 / 500000000000) (689035460543 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(9039 / 100000)
  have hx136 : Bounds (68728391637 / 100000000000) (344525910717 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((9039 / 100000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(90621 / 1000000)
  have hx137 : Bounds (344520166973 / 500000000000) (138162551411 / 200000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((90621 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (9039 / 100000) (90621 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(9039 / 100000) ≤ (344525910717 / 500000000000) := hx136.2
      have h2 : (689056422133 / 1000000000000) ≤ biasE (9039 / 100000) := hx114.1
      linarith
    · have h1 : biasE (90621 / 1000000) ≤ (689035460543 / 1000000000000) := hx135.2
      have h2 : (344520166973 / 500000000000) ≤ x93*(90621 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(90621 / 1000000)
  have hx139 : Bounds (1090621 / 1000000) (1090621 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90621 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(90621 / 1000000)
  have hx140 : Bounds (1090621 / 1000000) (1090621 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90621 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (43373629 / 500000000) (86747259 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4163.1) (by simpa only [div_one] using reflection_log_4163.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (94608381267 / 1000000000000) (47304191179 / 500000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(90621 / 1000000)
  have hx143 : Bounds (-90621 / 1000000) (-90621 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90621 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (909379 / 1000000) (909379 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(90621 / 1000000)
  have hx145 : Bounds (909379 / 1000000) (909379 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(90621 / 1000000)
  have hx146 : Bounds (-90621 / 1000000) (-90621 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90621 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (909379 / 1000000) (909379 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(90621 / 1000000)
  have hx148 : Bounds (909379 / 1000000) (909379 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-94993331 / 1000000000) (-9499333 / 100000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4164.1) (by simpa only [div_one] using reflection_log_4164.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-1349764693 / 15625000000) (-43192469721 / 500000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (1644688183 / 200000000000) (2055860729 / 250000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4111720457 / 1000000000000) (2055860729 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4111720457 / 1000000000000) (2055860729 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-2055860729 / 500000000000) (-4111720457 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (344517729271 / 500000000000) (689035460543 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (344517729271 / 500000000000) (689035460543 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (90621 / 1000000)
  have hx158 : Bounds (344517729271 / 500000000000) (689035460543 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(9039 / 100000)
  have hx160 : Bounds (109039 / 100000) (109039 / 100000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9039 / 100000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(9039 / 100000)
  have hx161 : Bounds (109039 / 100000) (109039 / 100000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9039 / 100000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (8653543 / 100000000) (86535431 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4161.1) (by simpa only [div_one] using reflection_log_4161.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (94357367517 / 1000000000000) (94357368609 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(9039 / 100000)
  have hx164 : Bounds (-9039 / 100000) (-9039 / 100000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9039 / 100000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (90961 / 100000) (90961 / 100000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(9039 / 100000)
  have hx166 : Bounds (90961 / 100000) (90961 / 100000) x166 := by
    exact hx165
  let x167 : ℝ := -(9039 / 100000)
  have hx167 : Bounds (-9039 / 100000) (-9039 / 100000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9039 / 100000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (90961 / 100000) (90961 / 100000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(9039 / 100000)
  have hx169 : Bounds (90961 / 100000) (90961 / 100000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-94739343 / 1000000000) (-47369671 / 500000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4162.1) (by simpa only [div_one] using reflection_log_4162.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-86175853787 / 1000000000000) (-21543963219 / 250000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (818151373 / 100000000000) (8181515733 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (818151373 / 200000000000) (4090757867 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (818151373 / 200000000000) (4090757867 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4090757867 / 1000000000000) (-818151373 / 200000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (689056422133 / 1000000000000) (137811284827 / 200000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (689056422133 / 1000000000000) (137811284827 / 200000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (9039 / 100000)
  have hx179 : Bounds (689056422133 / 1000000000000) (137811284827 / 200000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (344517729271 / 500000000000) (137811284827 / 200000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-8212165641 / 1000000000000) (-81703521 / 10000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-1030759 / 125000000) (-1025489 / 125000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4165.1) (by simpa only [div_one] using reflection_log_4166.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-1030759 / 250000000) (-1025489 / 250000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-1030759 / 250000000) (-1025489 / 250000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (1025489 / 250000000) (1030759 / 250000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (43578071 / 62500000) (697270217 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (43578071 / 62500000) (697270217 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (9039 / 100000) (90621 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-8212165641 / 1000000000000) (-81703521 / 10000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (109039 / 100000) (1090621 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-90621 / 1000000) (-9039 / 100000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (909379 / 1000000) (90961 / 100000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (909379 / 1000000) (90961 / 100000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (27484306461 / 25000000000) (549825760217 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (14984306461 / 12500000000) (299825760217 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (14984306461 / 12500000000) (299825760217 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (181274773 / 1000000000) (181740589 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4167.1) (by simpa only [div_one] using reflection_log_4168.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (181274773 / 2000000000) (181740589 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (181274773 / 2000000000) (181740589 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11799 / 10000) (59 / 50) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-9 / 50) (-1799 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (41 / 50) (8201 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (41 / 50) (8201 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1219363492257 / 1000000000000) (609756097561 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (719363492257 / 500000000000) (359756097561 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (719363492257 / 500000000000) (359756097561 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (90939671 / 250000000) (181982689 / 500000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4169.1) (by simpa only [div_one] using reflection_log_4170.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (90939671 / 500000000) (181982689 / 1000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (90939671 / 500000000) (181982689 / 1000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (43578071 / 31250000) (697270217 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (9039 / 100000) (90621 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-8212165641 / 1000000000000) (-81703521 / 10000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386286106359 / 1000000000000) (13863700819 / 10000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386286106359 / 1000000000000) (13863700819 / 10000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (191040056593 / 200000000000) (477643605581 / 500000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (85625356823 / 62500000000) (42813247543 / 31250000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (491821554191 / 500000000000) (491863025227 / 500000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (491821554191 / 500000000000) (491863025227 / 500000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1347596674267 / 1000000000000) (1347728221203 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (43578071 / 62500000) (697270217 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (121539089413 / 250000000000) (121546438879 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (338972100333 / 1000000000000) (339002847251 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (338972100333 / 1000000000000) (339002847251 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (228398837539 / 500000000000) (456883704309 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1094370395101 / 500000000000) (2189152998271 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2090685822137 / 1000000000000) (1045634931263 / 500000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2090685822137 / 1000000000000) (1045634931263 / 500000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-181740589 / 2000000000) (-181274773 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (43578071 / 31250000) (697270217 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (9039 / 100000) (90621 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-8212165641 / 1000000000000) (-81703521 / 10000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386286106359 / 1000000000000) (13863700819 / 10000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386286106359 / 1000000000000) (13863700819 / 10000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-125979857629 / 1000000000000) (-125649349621 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (201647531331 / 200000000000) (1008280163717 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (18226920357 / 200000000000) (91371356717 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (18226920357 / 200000000000) (91371356717 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (18226920357 / 100000000000) (91371356717 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (9039 / 50000) (90621 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-90621 / 500000) (-9039 / 50000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (102720357 / 100000000000) (981356717 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (102720357 / 100000000000) (981356717 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (353889841 / 500000000000) (1352420301 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-125272077947 / 1000000000000) (-3107423233 / 25000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (85625356823 / 62500000000) (42813247543 / 31250000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (491821554191 / 500000000000) (491863025227 / 500000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (491821554191 / 500000000000) (491863025227 / 500000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1347596674267 / 1000000000000) (1347728221203 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (43578071 / 62500000) (697270217 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (121539089413 / 250000000000) (121546438879 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (338972100333 / 1000000000000) (339002847251 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (338972100333 / 1000000000000) (339002847251 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (228398837539 / 500000000000) (456883704309 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1094370395101 / 500000000000) (2189152998271 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-137119872519 / 500000000000) (-272053759299 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-137119872519 / 500000000000) (-272053759299 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (9039 / 25000) (90621 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (201647531331 / 200000000000) (1008280163717 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (18226920357 / 50000000000) (73097085373 / 200000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (18226920357 / 50000000000) (73097085373 / 200000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (27117 / 100000) (271863 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (345761605301 / 500000000000) (691573273819 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (722989188461 / 500000000000) (180760382419 / 125000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (392105956469 / 1000000000000) (78627295753 / 200000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (392105956469 / 1000000000000) (78627295753 / 200000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-78627295753 / 200000000000) (-392105956469 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-228784573 / 8000000000) (-6655132401 / 250000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-228784573 / 8000000000) (-6655132401 / 250000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-14951571329 / 250000000000) (-2782758191 / 50000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-167023015177 / 500000000000) (-327708923119 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (43578071 / 31250000) (697270217 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (9039 / 100000) (90621 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (81703521 / 10000000000) (8212165641 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-8212165641 / 1000000000000) (-81703521 / 10000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386286106359 / 1000000000000) (13863700819 / 10000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386286106359 / 1000000000000) (13863700819 / 10000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (125306401153 / 1000000000000) (15704280399 / 125000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (991787834359 / 1000000000000) (9918296479 / 10000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (491821554191 / 500000000000) (491863025227 / 500000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (491821554191 / 500000000000) (491863025227 / 500000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (43578071 / 62500000) (697270217 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (121539089413 / 250000000000) (121546438879 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (121539089413 / 250000000000) (121546438879 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (1195510877 / 2500000000) (478273593061 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2090853466527 / 1000000000000) (41823124291 / 20000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (65499330807 / 250000000000) (65680207103 / 250000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (65499330807 / 250000000000) (65680207103 / 250000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (16440073723 / 1000000000000) (824572663 / 50000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (141095106453 / 200000000000) (141109575479 / 200000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (141095106453 / 200000000000) (141109575479 / 200000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (15552991457 / 31250000000) (497797807297 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (15552991457 / 31250000000) (497797807297 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-166287381447 / 1000000000000) (-40774832653 / 250000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2090685822137 / 500000000000) (1045634931263 / 250000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (16440073723 / 1000000000000) (824572663 / 50000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (141095106453 / 200000000000) (141109575479 / 200000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2949855386341 / 1000000000000) (2950982025131 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-181740589 / 2000000000) (-181274773 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (36403619 / 400000000) (36538121 / 400000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (36403619 / 400000000) (36538121 / 400000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (268463528973 / 1000000000000) (134779172879 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (51088073763 / 500000000000) (53229507573 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1799 / 10000) (9 / 50) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3236401 / 100000000) (81 / 2500) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3236401 / 100000000) (81 / 2500) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-81 / 2500) (-3236401 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (2419 / 2500) (96763599 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (2419 / 2500) (96763599 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (64590404497 / 62500000000) (1033484911121 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (64590404497 / 62500000000) (1033484911121 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (64590404497 / 62500000000) (1033484911121 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (5415204187 / 20000000000) (135759006001 / 500000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (93234089219 / 250000000000) (94494256787 / 250000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (344517729271 / 500000000000) (137811284827 / 200000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (59346232891 / 125000000000) (237399377821 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (59346232891 / 125000000000) (237399377821 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (177058943109 / 1000000000000) (22432877769 / 125000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (119404412129 / 250000000000) (477638438477 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2093633844019 / 1000000000000) (1046862488339 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (370696595679 / 1000000000000) (37574621187 / 100000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (370696595679 / 1000000000000) (37574621187 / 100000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (711618471085944139641354787 / 1872638818286560200000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_299 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1799 / 10000):ℝ) ((9 / 50)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (711618471085944139641354787 / 1872638818286560200000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (1797201 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (9009 / 100000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (9 / 50))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_299 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_299 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1799 / 10000):ℝ) ((9 / 50)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_299 ha ⟨hz.1.le,hz.2⟩ hs) (M := (711618471085944139641354787 / 1872638818286560200000000000))
  exact lt_of_lt_of_le (by norm_num : (711618471085944139641354787 / 1872638818286560200000000000) < 2*((1799 / 10000):ℝ)/(1-((1799 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0300 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_300 (a z s c : ℝ)
    (ha : Bounds (9 / 50) (1801 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (8991 / 100000) (1802801 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (4450005946521934241 / 11703122000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1801 / 10000)
  have hx1 : Bounds (11801 / 10000) (11801 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1801 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1801 / 10000)
  have hx2 : Bounds (11801 / 10000) (11801 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1801 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (8279959 / 50000000) (165599181 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4171.1) (by simpa only [div_one] using reflection_log_4171.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (97711796159 / 500000000000) (195423593499 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1801 / 10000)
  have hx5 : Bounds (-1801 / 10000) (-1801 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1801 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8199 / 10000) (8199 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1801 / 10000)
  have hx7 : Bounds (8199 / 10000) (8199 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1801 / 10000)
  have hx8 : Bounds (-1801 / 10000) (-1801 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1801 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8199 / 10000) (8199 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1801 / 10000)
  have hx10 : Bounds (8199 / 10000) (8199 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-99286449 / 500000000) (-198572897 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4172.1) (by simpa only [div_one] using reflection_log_4172.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-162809919071 / 1000000000000) (-651239673 / 4000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (32613673247 / 1000000000000) (32613675249 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (16306836623 / 1000000000000) (130454701 / 8000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (16306836623 / 1000000000000) (130454701 / 8000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-130454701 / 8000000000) (-16306836623 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (5414722739 / 8000000000) (676840344377 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (5414722739 / 8000000000) (676840344377 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1801 / 10000)
  have hx20 : Bounds (5414722739 / 8000000000) (676840344377 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(9 / 50)
  have hx22 : Bounds (59 / 50) (59 / 50) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 50) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(9 / 50)
  have hx23 : Bounds (59 / 50) (59 / 50) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 50) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (82757219 / 500000000) (165514439 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4157.1) (by simpa only [div_one] using reflection_log_4157.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (4882675921 / 25000000000) (9765351901 / 50000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(9 / 50)
  have hx26 : Bounds (-9 / 50) (-9 / 50) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 50) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (41 / 50) (41 / 50) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(9 / 50)
  have hx28 : Bounds (41 / 50) (41 / 50) x28 := by
    exact hx27
  let x29 : ℝ := -(9 / 50)
  have hx29 : Bounds (-9 / 50) (-9 / 50) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 50) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (41 / 50) (41 / 50) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(9 / 50)
  have hx31 : Bounds (41 / 50) (41 / 50) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-198450939 / 1000000000) (-99225469 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4158.1) (by simpa only [div_one] using reflection_log_4158.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-8136488499 / 50000000000) (-4068244229 / 25000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (1628863343 / 50000000000) (1628863443 / 50000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (1628863343 / 100000000000) (1628863443 / 100000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (1628863343 / 100000000000) (1628863443 / 100000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-1628863443 / 100000000000) (-1628863343 / 100000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (67685854557 / 100000000000) (67685854757 / 100000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (67685854557 / 100000000000) (67685854757 / 100000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (9 / 50)
  have hx41 : Bounds (67685854557 / 100000000000) (67685854757 / 100000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (5414722739 / 8000000000) (67685854757 / 100000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1801 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1801 / 10000000)
  have hx45 : Bounds (10001801 / 10000000) (10001801 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1801 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1801 / 10000000)
  have hx46 : Bounds (10001801 / 10000000) (10001801 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1801 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (180083 / 1000000000) (45021 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4173.1) (by simpa only [div_one] using reflection_log_4173.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (22514429 / 125000000000) (90058217 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1801 / 10000000)
  have hx49 : Bounds (-1801 / 10000000) (-1801 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1801 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998199 / 10000000) (9998199 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1801 / 10000000)
  have hx51 : Bounds (9998199 / 10000000) (9998199 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1801 / 10000000)
  have hx52 : Bounds (-1801 / 10000000) (-1801 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1801 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998199 / 10000000) (9998199 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1801 / 10000000)
  have hx54 : Bounds (9998199 / 10000000) (9998199 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-180117 / 1000000000) (-45029 / 250000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4174.1) (by simpa only [div_one] using reflection_log_4174.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-180084561 / 1000000000000) (-180083561 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (30871 / 1000000000000) (32873 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (3087 / 200000000000) (16437 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (3087 / 200000000000) (16437 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-16437 / 1000000000000) (-3087 / 200000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147163563 / 1000000000000) (138629433113 / 200000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147163563 / 1000000000000) (138629433113 / 200000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1801 / 10000000)
  have hx64 : Bounds (693147163563 / 1000000000000) (138629433113 / 200000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(0 / 1)
  have hx66 : Bounds (1 / 1) (1 / 1) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(0 / 1)
  have hx67 : Bounds (1 / 1) (1 / 1) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (0 / 1) (0 / 1) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (0 / 1) (0 / 1) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(0 / 1)
  have hx70 : Bounds (0 / 1) (0 / 1) x70 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1 / 1) (1 / 1) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(0 / 1)
  have hx72 : Bounds (1 / 1) (1 / 1) x72 := by
    exact hx71
  let x73 : ℝ := -(0 / 1)
  have hx73 : Bounds (0 / 1) (0 / 1) x73 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(0 / 1)
  have hx75 : Bounds (1 / 1) (1 / 1) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (0 / 1) (0 / 1) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (0 / 1) (0 / 1) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (0 / 1) (0 / 1) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (0 / 1)
  have hx85 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (693147163563 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (684993752969 / 500000000000) (137000572857 / 100000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (684993752969 / 1000000000000) (137000572857 / 200000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (684993752969 / 1000000000000) (137000572857 / 200000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (2773461962801 / 250000000000) (1390279168057 / 125000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7599216474463 / 1000000000000) (7618761698199 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7599216474463 / 1000000000000) (7618761698199 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(90441 / 1000000)
  have hx95 : Bounds (1090441 / 1000000) (1090441 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90441 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(90441 / 1000000)
  have hx96 : Bounds (1090441 / 1000000) (1090441 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90441 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (86582201 / 1000000000) (43291101 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4175.1) (by simpa only [div_one] using reflection_log_4175.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (1180159773 / 12500000000) (23603195733 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(90441 / 1000000)
  have hx99 : Bounds (-90441 / 1000000) (-90441 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90441 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (909559 / 1000000) (909559 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(90441 / 1000000)
  have hx101 : Bounds (909559 / 1000000) (909559 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(90441 / 1000000)
  have hx102 : Bounds (-90441 / 1000000) (-90441 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90441 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (909559 / 1000000) (909559 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(90441 / 1000000)
  have hx104 : Bounds (909559 / 1000000) (909559 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-94795413 / 1000000000) (-23698853 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4176.1) (by simpa only [div_one] using reflection_log_4176.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-86222021053 / 1000000000000) (-86222020143 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (8190760787 / 1000000000000) (8190762789 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4095380393 / 1000000000000) (819076279 / 200000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4095380393 / 1000000000000) (819076279 / 200000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-819076279 / 200000000000) (-4095380393 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (137810359721 / 200000000000) (689051800607 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (137810359721 / 200000000000) (689051800607 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (90441 / 1000000)
  have hx114 : Bounds (137810359721 / 200000000000) (689051800607 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(5667 / 62500)
  have hx116 : Bounds (68167 / 62500) (68167 / 62500) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5667 / 62500) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(5667 / 62500)
  have hx117 : Bounds (68167 / 62500) (68167 / 62500) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5667 / 62500) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (4339701 / 50000000) (86794021 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4177.1) (by simpa only [div_one] using reflection_log_4177.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (94663807381 / 1000000000000) (94663808473 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(5667 / 62500)
  have hx120 : Bounds (-5667 / 62500) (-5667 / 62500) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5667 / 62500) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (56833 / 62500) (56833 / 62500) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(5667 / 62500)
  have hx122 : Bounds (56833 / 62500) (56833 / 62500) x122 := by
    exact hx121
  let x123 : ℝ := -(5667 / 62500)
  have hx123 : Bounds (-5667 / 62500) (-5667 / 62500) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5667 / 62500) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (56833 / 62500) (56833 / 62500) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(5667 / 62500)
  have hx125 : Bounds (56833 / 62500) (56833 / 62500) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-47524707 / 500000000) (-95049413 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4178.1) (by simpa only [div_one] using reflection_log_4178.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-43215546767 / 500000000000) (-5401943289 / 62500000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (8232713847 / 1000000000000) (8232715849 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4116356923 / 1000000000000) (164654317 / 40000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4116356923 / 1000000000000) (164654317 / 40000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-164654317 / 40000000000) (-4116356923 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (27561232883 / 40000000000) (689030824077 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (27561232883 / 40000000000) (689030824077 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (5667 / 62500)
  have hx135 : Bounds (27561232883 / 40000000000) (689030824077 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(90441 / 1000000)
  have hx136 : Bounds (343640368583 / 500000000000) (689048426747 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((90441 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(5667 / 62500)
  have hx137 : Bounds (172259039043 / 250000000000) (6908083607 / 10000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((5667 / 62500) : ℝ)) <;> norm_num
  have hc : Bounds (90441 / 1000000) (5667 / 62500) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(90441 / 1000000) ≤ (689048426747 / 1000000000000) := hx136.2
      have h2 : (137810359721 / 200000000000) ≤ biasE (90441 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (5667 / 62500) ≤ (689030824077 / 1000000000000) := hx135.2
      have h2 : (172259039043 / 250000000000) ≤ x93*(5667 / 62500) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(5667 / 62500)
  have hx139 : Bounds (68167 / 62500) (68167 / 62500) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5667 / 62500) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(5667 / 62500)
  have hx140 : Bounds (68167 / 62500) (68167 / 62500) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5667 / 62500) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (4339701 / 50000000) (86794021 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4177.1) (by simpa only [div_one] using reflection_log_4177.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (94663807381 / 1000000000000) (94663808473 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(5667 / 62500)
  have hx143 : Bounds (-5667 / 62500) (-5667 / 62500) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5667 / 62500) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (56833 / 62500) (56833 / 62500) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(5667 / 62500)
  have hx145 : Bounds (56833 / 62500) (56833 / 62500) x145 := by
    exact hx144
  let x146 : ℝ := -(5667 / 62500)
  have hx146 : Bounds (-5667 / 62500) (-5667 / 62500) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5667 / 62500) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (56833 / 62500) (56833 / 62500) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(5667 / 62500)
  have hx148 : Bounds (56833 / 62500) (56833 / 62500) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-47524707 / 500000000) (-95049413 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4178.1) (by simpa only [div_one] using reflection_log_4178.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-43215546767 / 500000000000) (-5401943289 / 62500000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (8232713847 / 1000000000000) (8232715849 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4116356923 / 1000000000000) (164654317 / 40000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4116356923 / 1000000000000) (164654317 / 40000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-164654317 / 40000000000) (-4116356923 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (27561232883 / 40000000000) (689030824077 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (27561232883 / 40000000000) (689030824077 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (5667 / 62500)
  have hx158 : Bounds (27561232883 / 40000000000) (689030824077 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(90441 / 1000000)
  have hx160 : Bounds (1090441 / 1000000) (1090441 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90441 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(90441 / 1000000)
  have hx161 : Bounds (1090441 / 1000000) (1090441 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90441 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (86582201 / 1000000000) (43291101 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4175.1) (by simpa only [div_one] using reflection_log_4175.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (1180159773 / 12500000000) (23603195733 / 250000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(90441 / 1000000)
  have hx164 : Bounds (-90441 / 1000000) (-90441 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90441 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (909559 / 1000000) (909559 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(90441 / 1000000)
  have hx166 : Bounds (909559 / 1000000) (909559 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(90441 / 1000000)
  have hx167 : Bounds (-90441 / 1000000) (-90441 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90441 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (909559 / 1000000) (909559 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(90441 / 1000000)
  have hx169 : Bounds (909559 / 1000000) (909559 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-94795413 / 1000000000) (-23698853 / 250000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4176.1) (by simpa only [div_one] using reflection_log_4176.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-86222021053 / 1000000000000) (-86222020143 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (8190760787 / 1000000000000) (8190762789 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4095380393 / 1000000000000) (819076279 / 200000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4095380393 / 1000000000000) (819076279 / 200000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-819076279 / 200000000000) (-4095380393 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (137810359721 / 200000000000) (689051800607 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (137810359721 / 200000000000) (689051800607 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (90441 / 1000000)
  have hx179 : Bounds (137810359721 / 200000000000) (689051800607 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (27561232883 / 40000000000) (689051800607 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-32114889 / 3906250000) (-8179574481 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4127697 / 500000000) (-821321 / 100000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4179.1) (by simpa only [div_one] using reflection_log_4180.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4127697 / 1000000000) (-821321 / 200000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4127697 / 1000000000) (-821321 / 200000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (821321 / 200000000) (4127697 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (139450757 / 200000000) (348637439 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (139450757 / 200000000) (348637439 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (90441 / 1000000) (5667 / 62500) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-32114889 / 3906250000) (-8179574481 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1090441 / 1000000) (68167 / 62500) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-5667 / 62500) (-90441 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (56833 / 62500) (909559 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (56833 / 62500) (909559 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (274858475371 / 250000000000) (1099713194799 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (149858475371 / 125000000000) (599713194799 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (149858475371 / 125000000000) (599713194799 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (181377613 / 1000000000) (90921717 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4181.1) (by simpa only [div_one] using reflection_log_4182.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (181377613 / 2000000000) (90921717 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (181377613 / 2000000000) (90921717 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (59 / 50) (11801 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1801 / 10000) (-9 / 50) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8199 / 10000) (41 / 50) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8199 / 10000) (41 / 50) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1219512195121 / 1000000000000) (1219660934261 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (719512195121 / 500000000000) (719660934261 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (719512195121 / 500000000000) (719660934261 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (363965377 / 1000000000) (364172079 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4183.1) (by simpa only [div_one] using reflection_log_4184.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (363965377 / 2000000000) (364172079 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (363965377 / 2000000000) (364172079 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (139450757 / 100000000) (348637439 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (90441 / 1000000) (5667 / 62500) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-32114889 / 3906250000) (-8179574481 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (86642884901 / 62500000000) (1386370181519 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (86642884901 / 62500000000) (1386370181519 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (238798472841 / 250000000000) (238820217471 / 250000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (684993752969 / 500000000000) (137000572857 / 100000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (24590619211 / 25000000000) (983707756477 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (24590619211 / 25000000000) (983707756477 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1347553643293 / 1000000000000) (1347685261613 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (139450757 / 200000000) (348637439 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (60770355087 / 125000000000) (48619225549 / 100000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (338978880801 / 1000000000000) (5297025713 / 15625000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (338978880801 / 1000000000000) (5297025713 / 15625000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (228396112911 / 500000000000) (456878302963 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1094383333061 / 500000000000) (2189179113547 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (20906965491 / 10000000000) (1045640463961 / 500000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (20906965491 / 10000000000) (1045640463961 / 500000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-90921717 / 1000000000) (-181377613 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (139450757 / 100000000) (348637439 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (90441 / 1000000) (5667 / 62500) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-32114889 / 3906250000) (-8179574481 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (86642884901 / 62500000000) (1386370181519 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (86642884901 / 62500000000) (1386370181519 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-63025578651 / 500000000000) (-62860318587 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (100824703169 / 100000000000) (504144781749 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (91186869793 / 1000000000000) (45711815651 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (91186869793 / 1000000000000) (45711815651 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (91186869793 / 500000000000) (45711815651 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (90441 / 500000) (5667 / 31250) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-5667 / 31250) (-90441 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (514869793 / 500000000000) (491315651 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (514869793 / 500000000000) (491315651 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (709522313 / 1000000000000) (169270967 / 125000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-125341634989 / 1000000000000) (-62183234719 / 500000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (684993752969 / 500000000000) (137000572857 / 100000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (24590619211 / 25000000000) (983707756477 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (24590619211 / 25000000000) (983707756477 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1347553643293 / 1000000000000) (1347685261613 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (139450757 / 200000000) (348637439 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (60770355087 / 125000000000) (48619225549 / 100000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (338978880801 / 1000000000000) (5297025713 / 15625000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (338978880801 / 1000000000000) (5297025713 / 15625000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (228396112911 / 500000000000) (456878302963 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1094383333061 / 500000000000) (2189179113547 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-8574852793 / 31250000000) (-272209182689 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-8574852793 / 31250000000) (-272209182689 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (90441 / 250000) (5667 / 15625) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (100824703169 / 100000000000) (504144781749 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (91186869793 / 250000000000) (182847262603 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (91186869793 / 250000000000) (182847262603 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (271323 / 1000000) (17001 / 62500) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (138304274931 / 200000000000) (345785733101 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (722991078197 / 500000000000) (723043449307 / 500000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (392328216619 / 1000000000000) (196679386907 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (392328216619 / 1000000000000) (196679386907 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-196679386907 / 500000000000) (-392328216619 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-14305647321 / 500000000000) (-26633691413 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-14305647321 / 500000000000) (-26633691413 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-7479281851 / 125000000000) (-27841483363 / 500000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-41778693023 / 125000000000) (-65578429883 / 200000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (139450757 / 100000000) (348637439 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (90441 / 1000000) (5667 / 62500) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (8179574481 / 1000000000000) (32114889 / 3906250000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-32114889 / 3906250000) (-8179574481 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (86642884901 / 62500000000) (1386370181519 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (86642884901 / 62500000000) (1386370181519 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (125377106453 / 1000000000000) (125704957099 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (3874135111 / 3906250000) (991820425519 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (24590619211 / 25000000000) (983707756477 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (24590619211 / 25000000000) (983707756477 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (139450757 / 200000000) (348637439 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (60770355087 / 125000000000) (48619225549 / 100000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (60770355087 / 125000000000) (48619225549 / 100000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (478201811603 / 1000000000000) (95654218573 / 200000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2090864396611 / 1000000000000) (2091167318351 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (8192079001 / 31250000000) (262870098041 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (8192079001 / 31250000000) (262870098041 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (1645869633 / 100000000000) (8255052687 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (141097903681 / 200000000000) (705561905981 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (141097903681 / 200000000000) (705561905981 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (497715460579 / 1000000000000) (124454400793 / 250000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (497715460579 / 1000000000000) (124454400793 / 250000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-33277070119 / 200000000000) (-81598496083 / 500000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (20906965491 / 5000000000) (1045640463961 / 250000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (1645869633 / 100000000000) (8255052687 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (141097903681 / 200000000000) (705561905981 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2949929003111 / 1000000000000) (2951056314893 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-90921717 / 1000000000) (-181377613 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (182121943 / 2000000000) (91397233 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (182121943 / 2000000000) (91397233 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (268623400879 / 1000000000000) (269718381609 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (25559512571 / 250000000000) (106521389443 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (9 / 50) (1801 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (81 / 2500) (3243601 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (81 / 2500) (3243601 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3243601 / 100000000) (-81 / 2500) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96756399 / 100000000) (2419 / 2500) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96756399 / 100000000) (2419 / 2500) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (12918561389 / 12500000000) (1033523374511 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (12918561389 / 12500000000) (1033523374511 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (12918561389 / 12500000000) (1033523374511 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (270924481223 / 1000000000000) (135841195393 / 500000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (373162531507 / 1000000000000) (378203780229 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (27561232883 / 40000000000) (689051800607 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (474763473769 / 1000000000000) (5934904799 / 12500000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (474763473769 / 1000000000000) (5934904799 / 12500000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (88581969869 / 500000000000) (179568274423 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (238807243479 / 500000000000) (29852205539 / 62500000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2093647650869 / 1000000000000) (1046869418021 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (370918866251 / 1000000000000) (375969069881 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (370918866251 / 1000000000000) (375969069881 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (4450005946521934241 / 11703122000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_300 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((9 / 50):ℝ) ((1801 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (4450005946521934241 / 11703122000000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (8991 / 100000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1802801 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1801 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_300 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_300 {a z : ℝ}
    (ha : a ∈ Set.Icc ((9 / 50):ℝ) ((1801 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_300 ha ⟨hz.1.le,hz.2⟩ hs) (M := (4450005946521934241 / 11703122000000000000))
  exact lt_of_lt_of_le (by norm_num : (4450005946521934241 / 11703122000000000000) < 2*((9 / 50):ℝ)/(1-((9 / 50):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0301 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_301 (a z s c : ℝ)
    (ha : Bounds (1801 / 10000) (901 / 5000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1799199 / 20000000) (901901 / 10000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (356191705217247705711864037 / 936180074744720100000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(901 / 5000)
  have hx1 : Bounds (5901 / 5000) (5901 / 5000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((901 / 5000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(901 / 5000)
  have hx2 : Bounds (5901 / 5000) (5901 / 5000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((901 / 5000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (33136783 / 200000000) (41420979 / 250000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4185.1) (by simpa only [div_one] using reflection_log_4185.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (195540156483 / 1000000000000) (6110629927 / 31250000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(901 / 5000)
  have hx5 : Bounds (-901 / 5000) (-901 / 5000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((901 / 5000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (4099 / 5000) (4099 / 5000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(901 / 5000)
  have hx7 : Bounds (4099 / 5000) (4099 / 5000) x7 := by
    exact hx6
  let x8 : ℝ := -(901 / 5000)
  have hx8 : Bounds (-901 / 5000) (-901 / 5000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((901 / 5000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (4099 / 5000) (4099 / 5000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(901 / 5000)
  have hx10 : Bounds (4099 / 5000) (4099 / 5000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-198694871 / 1000000000) (-19869487 / 100000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4186.1) (by simpa only [div_one] using reflection_log_4186.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-81445027623 / 500000000000) (-81445027213 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (32650101237 / 1000000000000) (16325051619 / 500000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (8162525309 / 500000000000) (16325051619 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (8162525309 / 500000000000) (16325051619 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-16325051619 / 1000000000000) (-8162525309 / 500000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (676822128381 / 1000000000000) (338411065191 / 500000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (676822128381 / 1000000000000) (338411065191 / 500000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (901 / 5000)
  have hx20 : Bounds (676822128381 / 1000000000000) (338411065191 / 500000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1801 / 10000)
  have hx22 : Bounds (11801 / 10000) (11801 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1801 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1801 / 10000)
  have hx23 : Bounds (11801 / 10000) (11801 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1801 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (8279959 / 50000000) (165599181 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4171.1) (by simpa only [div_one] using reflection_log_4171.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (97711796159 / 500000000000) (195423593499 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1801 / 10000)
  have hx26 : Bounds (-1801 / 10000) (-1801 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1801 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8199 / 10000) (8199 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1801 / 10000)
  have hx28 : Bounds (8199 / 10000) (8199 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1801 / 10000)
  have hx29 : Bounds (-1801 / 10000) (-1801 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1801 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8199 / 10000) (8199 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1801 / 10000)
  have hx31 : Bounds (8199 / 10000) (8199 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-99286449 / 500000000) (-198572897 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4172.1) (by simpa only [div_one] using reflection_log_4172.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-162809919071 / 1000000000000) (-651239673 / 4000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (32613673247 / 1000000000000) (32613675249 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (16306836623 / 1000000000000) (130454701 / 8000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (16306836623 / 1000000000000) (130454701 / 8000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-130454701 / 8000000000) (-16306836623 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (5414722739 / 8000000000) (676840344377 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (5414722739 / 8000000000) (676840344377 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1801 / 10000)
  have hx41 : Bounds (5414722739 / 8000000000) (676840344377 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (676822128381 / 1000000000000) (676840344377 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (901 / 5000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(901 / 5000000)
  have hx45 : Bounds (5000901 / 5000000) (5000901 / 5000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((901 / 5000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(901 / 5000000)
  have hx46 : Bounds (5000901 / 5000000) (5000901 / 5000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((901 / 5000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (180183 / 1000000000) (22523 / 125000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4187.1) (by simpa only [div_one] using reflection_log_4187.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (45053867 / 250000000000) (18021647 / 100000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(901 / 5000000)
  have hx49 : Bounds (-901 / 5000000) (-901 / 5000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((901 / 5000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (4999099 / 5000000) (4999099 / 5000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(901 / 5000000)
  have hx51 : Bounds (4999099 / 5000000) (4999099 / 5000000) x51 := by
    exact hx50
  let x52 : ℝ := -(901 / 5000000)
  have hx52 : Bounds (-901 / 5000000) (-901 / 5000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((901 / 5000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (4999099 / 5000000) (4999099 / 5000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(901 / 5000000)
  have hx54 : Bounds (4999099 / 5000000) (4999099 / 5000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-180217 / 1000000000) (-22527 / 125000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4188.1) (by simpa only [div_one] using reflection_log_4188.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-7207381 / 40000000000) (-7207341 / 40000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (30943 / 1000000000000) (6589 / 200000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (15471 / 1000000000000) (16473 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (15471 / 1000000000000) (16473 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-16473 / 1000000000000) (-15471 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147163527 / 1000000000000) (693147165529 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147163527 / 1000000000000) (693147165529 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (901 / 5000000)
  have hx64 : Bounds (693147163527 / 1000000000000) (693147165529 / 1000000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(0 / 1)
  have hx66 : Bounds (1 / 1) (1 / 1) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(0 / 1)
  have hx67 : Bounds (1 / 1) (1 / 1) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (0 / 1) (0 / 1) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (0 / 1) (0 / 1) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(0 / 1)
  have hx70 : Bounds (0 / 1) (0 / 1) x70 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1 / 1) (1 / 1) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(0 / 1)
  have hx72 : Bounds (1 / 1) (1 / 1) x72 := by
    exact hx71
  let x73 : ℝ := -(0 / 1)
  have hx73 : Bounds (0 / 1) (0 / 1) x73 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(0 / 1)
  have hx75 : Bounds (1 / 1) (1 / 1) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (0 / 1) (0 / 1) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (0 / 1) (0 / 1) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (0 / 1) (0 / 1) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (0 / 1)
  have hx85 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (693147163527 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (342492322977 / 250000000000) (1369987525377 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (342492322977 / 500000000000) (684993762689 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (342492322977 / 500000000000) (684993762689 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (2771922860713 / 250000000000) (11116057756813 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7594898397429 / 1000000000000) (1903607557277 / 250000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7594898397429 / 1000000000000) (1903607557277 / 250000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(22623 / 250000)
  have hx95 : Bounds (272623 / 250000) (272623 / 250000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((22623 / 250000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(22623 / 250000)
  have hx96 : Bounds (272623 / 250000) (272623 / 250000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((22623 / 250000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (8662897 / 100000000) (86628971 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4189.1) (by simpa only [div_one] using reflection_log_4189.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (94468198753 / 1000000000000) (23617049961 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(22623 / 250000)
  have hx99 : Bounds (-22623 / 250000) (-22623 / 250000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((22623 / 250000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (227377 / 250000) (227377 / 250000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(22623 / 250000)
  have hx101 : Bounds (227377 / 250000) (227377 / 250000) x101 := by
    exact hx100
  let x102 : ℝ := -(22623 / 250000)
  have hx102 : Bounds (-22623 / 250000) (-22623 / 250000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((22623 / 250000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (227377 / 250000) (227377 / 250000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(22623 / 250000)
  have hx104 : Bounds (227377 / 250000) (227377 / 250000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-47425743 / 500000000) (-18970297 / 200000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4190.1) (by simpa only [div_one] using reflection_log_4190.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-86268185329 / 1000000000000) (-86268184419 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (512500839 / 62500000000) (328000617 / 40000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (512500839 / 125000000000) (4100007713 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (512500839 / 125000000000) (4100007713 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4100007713 / 1000000000000) (-512500839 / 125000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (689047172287 / 1000000000000) (43065448393 / 62500000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (689047172287 / 1000000000000) (43065448393 / 62500000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (22623 / 250000)
  have hx114 : Bounds (689047172287 / 1000000000000) (43065448393 / 62500000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(90723 / 1000000)
  have hx116 : Bounds (1090723 / 1000000) (1090723 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90723 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(90723 / 1000000)
  have hx117 : Bounds (1090723 / 1000000) (1090723 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90723 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (86840779 / 1000000000) (4342039 / 50000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4191.1) (by simpa only [div_one] using reflection_log_4191.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (94719234993 / 1000000000000) (23679809021 / 250000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(90723 / 1000000)
  have hx120 : Bounds (-90723 / 1000000) (-90723 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90723 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (909277 / 1000000) (909277 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(90723 / 1000000)
  have hx122 : Bounds (909277 / 1000000) (909277 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(90723 / 1000000)
  have hx123 : Bounds (-90723 / 1000000) (-90723 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90723 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (909277 / 1000000) (909277 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(90723 / 1000000)
  have hx125 : Bounds (909277 / 1000000) (909277 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-95105501 / 1000000000) (-190211 / 2000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4192.1) (by simpa only [div_one] using reflection_log_4192.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-86477244633 / 1000000000000) (-86477243723 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (206049759 / 25000000000) (8241992361 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (206049759 / 50000000000) (4120996181 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (206049759 / 50000000000) (4120996181 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4120996181 / 1000000000000) (-206049759 / 50000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (689026183819 / 1000000000000) (34451309291 / 50000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (689026183819 / 1000000000000) (34451309291 / 50000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (90723 / 1000000)
  have hx135 : Bounds (689026183819 / 1000000000000) (34451309291 / 50000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(22623 / 250000)
  have hx136 : Bounds (34363877289 / 50000000000) (689045020293 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((22623 / 250000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(90723 / 1000000)
  have hx137 : Bounds (689031967309 / 1000000000000) (172700988419 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((90723 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (22623 / 250000) (90723 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(22623 / 250000) ≤ (689045020293 / 1000000000000) := hx136.2
      have h2 : (689047172287 / 1000000000000) ≤ biasE (22623 / 250000) := hx114.1
      linarith
    · have h1 : biasE (90723 / 1000000) ≤ (34451309291 / 50000000000) := hx135.2
      have h2 : (689031967309 / 1000000000000) ≤ x93*(90723 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(90723 / 1000000)
  have hx139 : Bounds (1090723 / 1000000) (1090723 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90723 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(90723 / 1000000)
  have hx140 : Bounds (1090723 / 1000000) (1090723 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90723 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (86840779 / 1000000000) (4342039 / 50000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4191.1) (by simpa only [div_one] using reflection_log_4191.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (94719234993 / 1000000000000) (23679809021 / 250000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(90723 / 1000000)
  have hx143 : Bounds (-90723 / 1000000) (-90723 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90723 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (909277 / 1000000) (909277 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(90723 / 1000000)
  have hx145 : Bounds (909277 / 1000000) (909277 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(90723 / 1000000)
  have hx146 : Bounds (-90723 / 1000000) (-90723 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90723 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (909277 / 1000000) (909277 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(90723 / 1000000)
  have hx148 : Bounds (909277 / 1000000) (909277 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-95105501 / 1000000000) (-190211 / 2000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4192.1) (by simpa only [div_one] using reflection_log_4192.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-86477244633 / 1000000000000) (-86477243723 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (206049759 / 25000000000) (8241992361 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (206049759 / 50000000000) (4120996181 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (206049759 / 50000000000) (4120996181 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4120996181 / 1000000000000) (-206049759 / 50000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (689026183819 / 1000000000000) (34451309291 / 50000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (689026183819 / 1000000000000) (34451309291 / 50000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (90723 / 1000000)
  have hx158 : Bounds (689026183819 / 1000000000000) (34451309291 / 50000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(22623 / 250000)
  have hx160 : Bounds (272623 / 250000) (272623 / 250000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((22623 / 250000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(22623 / 250000)
  have hx161 : Bounds (272623 / 250000) (272623 / 250000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((22623 / 250000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (8662897 / 100000000) (86628971 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4189.1) (by simpa only [div_one] using reflection_log_4189.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (94468198753 / 1000000000000) (23617049961 / 250000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(22623 / 250000)
  have hx164 : Bounds (-22623 / 250000) (-22623 / 250000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((22623 / 250000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (227377 / 250000) (227377 / 250000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(22623 / 250000)
  have hx166 : Bounds (227377 / 250000) (227377 / 250000) x166 := by
    exact hx165
  let x167 : ℝ := -(22623 / 250000)
  have hx167 : Bounds (-22623 / 250000) (-22623 / 250000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((22623 / 250000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (227377 / 250000) (227377 / 250000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(22623 / 250000)
  have hx169 : Bounds (227377 / 250000) (227377 / 250000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-47425743 / 500000000) (-18970297 / 200000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4190.1) (by simpa only [div_one] using reflection_log_4190.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-86268185329 / 1000000000000) (-86268184419 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (512500839 / 62500000000) (328000617 / 40000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (512500839 / 125000000000) (4100007713 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (512500839 / 125000000000) (4100007713 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4100007713 / 1000000000000) (-512500839 / 125000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (689047172287 / 1000000000000) (43065448393 / 62500000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (689047172287 / 1000000000000) (43065448393 / 62500000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (22623 / 250000)
  have hx179 : Bounds (689047172287 / 1000000000000) (43065448393 / 62500000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (689026183819 / 1000000000000) (43065448393 / 62500000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-8230662729 / 1000000000000) (-511800129 / 62500000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4132361 / 500000000) (-4111257 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4193.1) (by simpa only [div_one] using reflection_log_4194.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4132361 / 1000000000) (-4111257 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4132361 / 1000000000) (-4111257 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (4111257 / 1000000000) (4132361 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (697258437 / 1000000000) (348639771 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (697258437 / 1000000000) (348639771 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (22623 / 250000) (90723 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-8230662729 / 1000000000000) (-511800129 / 62500000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (272623 / 250000) (1090723 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-90723 / 1000000) (-22623 / 250000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (909277 / 1000000) (227377 / 250000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (909277 / 1000000) (227377 / 250000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (13743694393 / 12500000000) (1099774876083 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (7493694393 / 6250000000) (599774876083 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (7493694393 / 6250000000) (599774876083 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (36296091 / 200000000) (4548657 / 25000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4195.1) (by simpa only [div_one] using reflection_log_4196.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (36296091 / 400000000) (4548657 / 50000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (36296091 / 400000000) (4548657 / 50000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11801 / 10000) (5901 / 5000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-901 / 5000) (-1801 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (4099 / 5000) (8199 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (4099 / 5000) (8199 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (60983046713 / 50000000000) (609904854843 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (35983046713 / 25000000000) (359904854843 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (35983046713 / 25000000000) (359904854843 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (182086039 / 500000000) (364378787 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4197.1) (by simpa only [div_one] using reflection_log_4198.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (182086039 / 1000000000) (364378787 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (182086039 / 1000000000) (364378787 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (697258437 / 500000000) (348639771 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (22623 / 250000) (90723 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-8230662729 / 1000000000000) (-511800129 / 62500000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386286211271 / 1000000000000) (86648142621 / 62500000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386286211271 / 1000000000000) (86648142621 / 62500000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (119398437229 / 125000000000) (191054905057 / 200000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (342492322977 / 250000000000) (684993762689 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (19672128367 / 20000000000) (15370147693 / 15625000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (19672128367 / 20000000000) (15370147693 / 15625000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1347510588463 / 1000000000000) (1347642278569 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (697258437 / 1000000000) (348639771 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (486169327967 / 1000000000000) (121549689923 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (67797133147 / 200000000000) (2118852803 / 6250000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (67797133147 / 200000000000) (2118852803 / 6250000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (91357354783 / 200000000000) (228436449551 / 500000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1094396277351 / 500000000000) (273650655269 / 125000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2090707283599 / 1000000000000) (2091291998449 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2090707283599 / 1000000000000) (2091291998449 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-4548657 / 50000000) (-36296091 / 400000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (697258437 / 500000000) (348639771 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (22623 / 250000) (90723 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-8230662729 / 1000000000000) (-511800129 / 62500000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386286211271 / 1000000000000) (86648142621 / 62500000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386286211271 / 1000000000000) (86648142621 / 62500000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-126122457751 / 1000000000000) (-12579192619 / 100000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1008256412189 / 1000000000000) (504149484371 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (91239139251 / 1000000000000) (45737953671 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (91239139251 / 1000000000000) (45737953671 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (91239139251 / 500000000000) (45737953671 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (22623 / 125000) (90723 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-90723 / 500000) (-22623 / 125000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (516139251 / 500000000000) (491953671 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (516139251 / 500000000000) (491953671 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (177816729 / 250000000000) (338979287 / 250000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-25082238167 / 200000000000) (-62218004521 / 500000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (342492322977 / 250000000000) (684993762689 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (19672128367 / 20000000000) (15370147693 / 15625000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (19672128367 / 20000000000) (15370147693 / 15625000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1347510588463 / 1000000000000) (1347642278569 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (697258437 / 1000000000) (348639771 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (486169327967 / 1000000000000) (121549689923 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (67797133147 / 200000000000) (2118852803 / 6250000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (67797133147 / 200000000000) (2118852803 / 6250000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (91357354783 / 200000000000) (228436449551 / 500000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1094396277351 / 500000000000) (273650655269 / 125000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-274550836401 / 1000000000000) (-272364610127 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-274550836401 / 1000000000000) (-272364610127 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (22623 / 62500) (90723 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1008256412189 / 1000000000000) (504149484371 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (364956557007 / 1000000000000) (73180725873 / 200000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (364956557007 / 1000000000000) (73180725873 / 200000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (67869 / 250000) (272169 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (69151953797 / 100000000000) (86446207231 / 125000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1445985937427 / 1000000000000) (18076134243 / 12500000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (98137619587 / 250000000000) (393581070463 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (98137619587 / 250000000000) (393581070463 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-393581070463 / 1000000000000) (-98137619587 / 250000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-1789032091 / 62500000000) (-26646848983 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-1789032091 / 62500000000) (-26646848983 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-59862215951 / 1000000000000) (-55710761253 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-5225203943 / 15625000000) (-16403768569 / 50000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (697258437 / 500000000) (348639771 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (22623 / 250000) (90723 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (511800129 / 62500000000) (8230662729 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-8230662729 / 1000000000000) (-511800129 / 62500000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386286211271 / 1000000000000) (86648142621 / 62500000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386286211271 / 1000000000000) (86648142621 / 62500000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (12544781183 / 100000000000) (125775671089 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (991769337271 / 1000000000000) (61988199871 / 62500000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (19672128367 / 20000000000) (15370147693 / 15625000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (19672128367 / 20000000000) (15370147693 / 15625000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (697258437 / 1000000000) (348639771 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (486169327967 / 1000000000000) (121549689923 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (486169327967 / 1000000000000) (121549689923 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (478199271393 / 1000000000000) (59783573957 / 125000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2090875331239 / 1000000000000) (2091178426699 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (262295735113 / 1000000000000) (52603873997 / 200000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (262295735113 / 1000000000000) (52603873997 / 200000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (16477329841 / 1000000000000) (16528768347 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (35275175683 / 50000000000) (141115188527 / 200000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (35275175683 / 50000000000) (141115188527 / 200000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (248867603893 / 500000000000) (248918705413 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (248867603893 / 500000000000) (248918705413 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-16648332813 / 100000000000) (-163294663143 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2090707283599 / 500000000000) (2091291998449 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (16477329841 / 1000000000000) (16528768347 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (35275175683 / 50000000000) (141115188527 / 200000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2950002669227 / 1000000000000) (1475565323131 / 500000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-4548657 / 50000000) (-36296091 / 400000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (91112899 / 1000000000) (45724583 / 500000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (91112899 / 1000000000) (45724583 / 500000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (268783295251 / 1000000000000) (134939218179 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (102299967121 / 1000000000000) (21316754643 / 200000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1801 / 10000) (901 / 5000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3243601 / 100000000) (811801 / 25000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3243601 / 100000000) (811801 / 25000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-811801 / 25000000) (-3243601 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (24188199 / 25000000) (96756399 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (24188199 / 25000000) (96756399 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (103352337451 / 100000000000) (103356186213 / 100000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (103352337451 / 100000000000) (103356186213 / 100000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (103352337451 / 100000000000) (103356186213 / 100000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (271088773273 / 1000000000000) (135923394909 / 500000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (186694370197 / 500000000000) (378430563033 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (689026183819 / 1000000000000) (43065448393 / 62500000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (118689270497 / 250000000000) (94957201679 / 200000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (118689270497 / 250000000000) (94957201679 / 200000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (44317237209 / 250000000000) (89836768239 / 500000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (238805661803 / 500000000000) (477632137121 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (1046830732567 / 500000000000) (1046876351727 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (185570583571 / 500000000000) (18809597637 / 50000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (185570583571 / 500000000000) (18809597637 / 50000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (356191705217247705711864037 / 936180074744720100000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_301 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1801 / 10000):ℝ) ((901 / 5000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (356191705217247705711864037 / 936180074744720100000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (1799199 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (901901 / 10000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (901 / 5000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_301 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_301 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1801 / 10000):ℝ) ((901 / 5000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_301 ha ⟨hz.1.le,hz.2⟩ hs) (M := (356191705217247705711864037 / 936180074744720100000000000))
  exact lt_of_lt_of_le (by norm_num : (356191705217247705711864037 / 936180074744720100000000000) < 2*((1801 / 10000):ℝ)/(1-((1801 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0302 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_302 (a z s c : ℝ)
    (ha : Bounds (901 / 5000) (1803 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (900099 / 10000000) (1804803 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (8909573135529087979805669 / 23402758834544040000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1803 / 10000)
  have hx1 : Bounds (11803 / 10000) (11803 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1803 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1803 / 10000)
  have hx2 : Bounds (11803 / 10000) (11803 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1803 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (165768643 / 1000000000) (41442161 / 250000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4199.1) (by simpa only [div_one] using reflection_log_4199.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (48914182333 / 250000000000) (97828365257 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1803 / 10000)
  have hx5 : Bounds (-1803 / 10000) (-1803 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1803 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8197 / 10000) (8197 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1803 / 10000)
  have hx7 : Bounds (8197 / 10000) (8197 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1803 / 10000)
  have hx8 : Bounds (-1803 / 10000) (-1803 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1803 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8197 / 10000) (8197 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1803 / 10000)
  have hx10 : Bounds (8197 / 10000) (8197 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-9940843 / 50000000) (-198816859 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4200.1) (by simpa only [div_one] using reflection_log_4200.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-81485090071 / 500000000000) (-81485089661 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (3268654919 / 100000000000) (4085818899 / 125000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (3268654919 / 200000000000) (4085818899 / 250000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (3268654919 / 200000000000) (4085818899 / 250000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-4085818899 / 250000000000) (-3268654919 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (169200976101 / 250000000000) (135360781281 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (169200976101 / 250000000000) (135360781281 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1803 / 10000)
  have hx20 : Bounds (169200976101 / 250000000000) (135360781281 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(901 / 5000)
  have hx22 : Bounds (5901 / 5000) (5901 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((901 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(901 / 5000)
  have hx23 : Bounds (5901 / 5000) (5901 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((901 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (33136783 / 200000000) (41420979 / 250000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4185.1) (by simpa only [div_one] using reflection_log_4185.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (195540156483 / 1000000000000) (6110629927 / 31250000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(901 / 5000)
  have hx26 : Bounds (-901 / 5000) (-901 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((901 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4099 / 5000) (4099 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(901 / 5000)
  have hx28 : Bounds (4099 / 5000) (4099 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(901 / 5000)
  have hx29 : Bounds (-901 / 5000) (-901 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((901 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4099 / 5000) (4099 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(901 / 5000)
  have hx31 : Bounds (4099 / 5000) (4099 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-198694871 / 1000000000) (-19869487 / 100000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4186.1) (by simpa only [div_one] using reflection_log_4186.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-81445027623 / 500000000000) (-81445027213 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (32650101237 / 1000000000000) (16325051619 / 500000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (8162525309 / 500000000000) (16325051619 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (8162525309 / 500000000000) (16325051619 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-16325051619 / 1000000000000) (-8162525309 / 500000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (676822128381 / 1000000000000) (338411065191 / 500000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (676822128381 / 1000000000000) (338411065191 / 500000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (901 / 5000)
  have hx41 : Bounds (676822128381 / 1000000000000) (338411065191 / 500000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (169200976101 / 250000000000) (338411065191 / 500000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1803 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1803 / 10000000)
  have hx45 : Bounds (10001803 / 10000000) (10001803 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1803 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1803 / 10000000)
  have hx46 : Bounds (10001803 / 10000000) (10001803 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1803 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (180283 / 1000000000) (45071 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4201.1) (by simpa only [div_one] using reflection_log_4201.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (36063101 / 200000000000) (90158253 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1803 / 10000000)
  have hx49 : Bounds (-1803 / 10000000) (-1803 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1803 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998197 / 10000000) (9998197 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1803 / 10000000)
  have hx51 : Bounds (9998197 / 10000000) (9998197 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1803 / 10000000)
  have hx52 : Bounds (-1803 / 10000000) (-1803 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1803 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998197 / 10000000) (9998197 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1803 / 10000000)
  have hx54 : Bounds (9998197 / 10000000) (9998197 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-180317 / 1000000000) (-45079 / 250000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4202.1) (by simpa only [div_one] using reflection_log_4202.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-180284489 / 1000000000000) (-180283489 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (3877 / 125000000000) (33017 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (3877 / 250000000000) (16509 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (3877 / 250000000000) (16509 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-16509 / 1000000000000) (-3877 / 250000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147163491 / 1000000000000) (173286791373 / 250000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147163491 / 1000000000000) (173286791373 / 250000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1803 / 10000000)
  have hx64 : Bounds (693147163491 / 1000000000000) (173286791373 / 250000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(0 / 1)
  have hx66 : Bounds (1 / 1) (1 / 1) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(0 / 1)
  have hx67 : Bounds (1 / 1) (1 / 1) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (0 / 1) (0 / 1) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (0 / 1) (0 / 1) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(0 / 1)
  have hx70 : Bounds (0 / 1) (0 / 1) x70 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1 / 1) (1 / 1) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(0 / 1)
  have hx72 : Bounds (1 / 1) (1 / 1) x72 := by
    exact hx71
  let x73 : ℝ := -(0 / 1)
  have hx73 : Bounds (0 / 1) (0 / 1) x73 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(0 / 1)
  have hx75 : Bounds (1 / 1) (1 / 1) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (0 / 1) (0 / 1) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (0 / 1) (0 / 1) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (0 / 1) (0 / 1) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (0 / 1)
  have hx85 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (693147163491 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (273990213579 / 200000000000) (684984655691 / 500000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (684975533947 / 1000000000000) (684984655691 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (684975533947 / 1000000000000) (684984655691 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (11081541863571 / 1000000000000) (11109889023319 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (1518117010991 / 200000000000) (1902525876851 / 250000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (1518117010991 / 200000000000) (1902525876851 / 250000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(90543 / 1000000)
  have hx95 : Bounds (1090543 / 1000000) (1090543 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90543 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(90543 / 1000000)
  have hx96 : Bounds (1090543 / 1000000) (1090543 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90543 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (86675737 / 1000000000) (43337869 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4203.1) (by simpa only [div_one] using reflection_log_4203.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (18904723651 / 200000000000) (47261809673 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(90543 / 1000000)
  have hx99 : Bounds (-90543 / 1000000) (-90543 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90543 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (909457 / 1000000) (909457 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(90543 / 1000000)
  have hx101 : Bounds (909457 / 1000000) (909457 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(90543 / 1000000)
  have hx102 : Bounds (-90543 / 1000000) (-90543 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90543 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (909457 / 1000000) (909457 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(90543 / 1000000)
  have hx104 : Bounds (909457 / 1000000) (909457 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-94907561 / 1000000000) (-2372689 / 25000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4204.1) (by simpa only [div_one] using reflection_log_4204.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-17262869141 / 200000000000) (-43157172397 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (164185451 / 20000000000) (1026159319 / 125000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (164185451 / 40000000000) (1026159319 / 250000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (164185451 / 40000000000) (1026159319 / 250000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-1026159319 / 250000000000) (-164185451 / 40000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (172260635681 / 250000000000) (27561701789 / 40000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (172260635681 / 250000000000) (27561701789 / 40000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (90543 / 1000000)
  have hx114 : Bounds (172260635681 / 250000000000) (27561701789 / 40000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(45387 / 500000)
  have hx116 : Bounds (545387 / 500000) (545387 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45387 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(45387 / 500000)
  have hx117 : Bounds (545387 / 500000) (545387 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45387 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (17377507 / 200000000) (5430471 / 62500000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4205.1) (by simpa only [div_one] using reflection_log_4205.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (47387332051 / 500000000000) (94774665193 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(45387 / 500000)
  have hx120 : Bounds (-45387 / 500000) (-45387 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45387 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (454613 / 500000) (454613 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(45387 / 500000)
  have hx122 : Bounds (454613 / 500000) (454613 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(45387 / 500000)
  have hx123 : Bounds (-45387 / 500000) (-45387 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45387 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (454613 / 500000) (454613 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(45387 / 500000)
  have hx125 : Bounds (454613 / 500000) (454613 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-95161591 / 1000000000) (-9516159 / 100000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4206.1) (by simpa only [div_one] using reflection_log_4206.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-86523392739 / 1000000000000) (-86523391829 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (8251271363 / 1000000000000) (2062818341 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4125635681 / 1000000000000) (2062818341 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4125635681 / 1000000000000) (2062818341 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2062818341 / 500000000000) (-4125635681 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (344510771659 / 500000000000) (689021545319 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (344510771659 / 500000000000) (689021545319 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (45387 / 500000)
  have hx135 : Bounds (344510771659 / 500000000000) (689021545319 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(90543 / 1000000)
  have hx136 : Bounds (68727434263 / 100000000000) (689041601871 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((90543 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(45387 / 500000)
  have hx137 : Bounds (344513883889 / 500000000000) (345399767891 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((45387 / 500000) : ℝ)) <;> norm_num
  have hc : Bounds (90543 / 1000000) (45387 / 500000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(90543 / 1000000) ≤ (689041601871 / 1000000000000) := hx136.2
      have h2 : (172260635681 / 250000000000) ≤ biasE (90543 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (45387 / 500000) ≤ (689021545319 / 1000000000000) := hx135.2
      have h2 : (344513883889 / 500000000000) ≤ x93*(45387 / 500000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(45387 / 500000)
  have hx139 : Bounds (545387 / 500000) (545387 / 500000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45387 / 500000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(45387 / 500000)
  have hx140 : Bounds (545387 / 500000) (545387 / 500000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45387 / 500000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (17377507 / 200000000) (5430471 / 62500000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4205.1) (by simpa only [div_one] using reflection_log_4205.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (47387332051 / 500000000000) (94774665193 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(45387 / 500000)
  have hx143 : Bounds (-45387 / 500000) (-45387 / 500000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45387 / 500000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (454613 / 500000) (454613 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(45387 / 500000)
  have hx145 : Bounds (454613 / 500000) (454613 / 500000) x145 := by
    exact hx144
  let x146 : ℝ := -(45387 / 500000)
  have hx146 : Bounds (-45387 / 500000) (-45387 / 500000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45387 / 500000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (454613 / 500000) (454613 / 500000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(45387 / 500000)
  have hx148 : Bounds (454613 / 500000) (454613 / 500000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-95161591 / 1000000000) (-9516159 / 100000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4206.1) (by simpa only [div_one] using reflection_log_4206.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-86523392739 / 1000000000000) (-86523391829 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (8251271363 / 1000000000000) (2062818341 / 250000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4125635681 / 1000000000000) (2062818341 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4125635681 / 1000000000000) (2062818341 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-2062818341 / 500000000000) (-4125635681 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (344510771659 / 500000000000) (689021545319 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (344510771659 / 500000000000) (689021545319 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (45387 / 500000)
  have hx158 : Bounds (344510771659 / 500000000000) (689021545319 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(90543 / 1000000)
  have hx160 : Bounds (1090543 / 1000000) (1090543 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90543 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(90543 / 1000000)
  have hx161 : Bounds (1090543 / 1000000) (1090543 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90543 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (86675737 / 1000000000) (43337869 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4203.1) (by simpa only [div_one] using reflection_log_4203.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (18904723651 / 200000000000) (47261809673 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(90543 / 1000000)
  have hx164 : Bounds (-90543 / 1000000) (-90543 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90543 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (909457 / 1000000) (909457 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(90543 / 1000000)
  have hx166 : Bounds (909457 / 1000000) (909457 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(90543 / 1000000)
  have hx167 : Bounds (-90543 / 1000000) (-90543 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90543 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (909457 / 1000000) (909457 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(90543 / 1000000)
  have hx169 : Bounds (909457 / 1000000) (909457 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-94907561 / 1000000000) (-2372689 / 25000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4204.1) (by simpa only [div_one] using reflection_log_4204.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-17262869141 / 200000000000) (-43157172397 / 500000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (164185451 / 20000000000) (1026159319 / 125000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (164185451 / 40000000000) (1026159319 / 250000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (164185451 / 40000000000) (1026159319 / 250000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-1026159319 / 250000000000) (-164185451 / 40000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (172260635681 / 250000000000) (27561701789 / 40000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (172260635681 / 250000000000) (27561701789 / 40000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (90543 / 1000000)
  have hx179 : Bounds (172260635681 / 250000000000) (27561701789 / 40000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (344510771659 / 500000000000) (27561701789 / 40000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-2059979769 / 250000000000) (-8198034849 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-1654811 / 200000000) (-8231823 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4207.1) (by simpa only [div_one] using reflection_log_4208.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-1654811 / 400000000) (-8231823 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-1654811 / 400000000) (-8231823 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (8231823 / 2000000000) (1654811 / 400000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1394526183 / 2000000000) (1394568417 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1394526183 / 2000000000) (1394568417 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (90543 / 1000000) (45387 / 500000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-2059979769 / 250000000000) (-8198034849 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1090543 / 1000000) (545387 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-45387 / 500000) (-90543 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (454613 / 500000) (909457 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (454613 / 500000) (909457 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (137444651039 / 125000000000) (1099836564287 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (74944651039 / 62500000000) (599836564287 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (74944651039 / 62500000000) (599836564287 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (90791649 / 500000000) (182049127 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4209.1) (by simpa only [div_one] using reflection_log_4210.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (90791649 / 1000000000) (182049127 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (90791649 / 1000000000) (182049127 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (5901 / 5000) (11803 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1803 / 10000) (-901 / 5000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8197 / 10000) (4099 / 5000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8197 / 10000) (4099 / 5000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (243961941937 / 200000000000) (1219958521411 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (143961941937 / 100000000000) (719958521411 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (143961941937 / 100000000000) (719958521411 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (182189393 / 500000000) (364585503 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4211.1) (by simpa only [div_one] using reflection_log_4212.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (182189393 / 1000000000) (364585503 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (182189393 / 1000000000) (364585503 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1394526183 / 1000000000) (1394568417 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (90543 / 1000000) (45387 / 500000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-2059979769 / 250000000000) (-8198034849 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (346571565981 / 250000000000) (1386370382151 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (346571565981 / 250000000000) (1386370382151 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (955181101049 / 1000000000000) (955268176049 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (684975533947 / 500000000000) (684984655691 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (491794029057 / 500000000000) (491835569039 / 500000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (491794029057 / 500000000000) (491835569039 / 500000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1347467510581 / 1000000000000) (67379963583 / 50000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1394526183 / 2000000000) (1394568417 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (30385988673 / 62500000000) (15193914607 / 31250000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169496227203 / 500000000000) (67804651013 / 200000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169496227203 / 500000000000) (67804651013 / 200000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (114195329661 / 250000000000) (228433745801 / 500000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (218881846133 / 100000000000) (2189231387503 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2090718027889 / 1000000000000) (209130307449 / 100000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2090718027889 / 1000000000000) (209130307449 / 100000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-182049127 / 2000000000) (-90791649 / 1000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1394526183 / 1000000000) (1394568417 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (90543 / 1000000) (45387 / 500000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-2059979769 / 250000000000) (-8198034849 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (346571565981 / 250000000000) (1386370382151 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (346571565981 / 250000000000) (1386370382151 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-25238751777 / 200000000000) (-125863215887 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (20165315963 / 20000000000) (1008308379451 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (91291410161 / 1000000000000) (91528184837 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (91291410161 / 1000000000000) (91528184837 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (91291410161 / 500000000000) (91528184837 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (90543 / 500000) (45387 / 250000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-45387 / 250000) (-90543 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (517410161 / 500000000000) (985184837 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (517410161 / 500000000000) (985184837 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (142602699 / 200000000000) (271533707 / 200000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-12548074539 / 100000000000) (-15563193419 / 125000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (684975533947 / 500000000000) (684984655691 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (491794029057 / 500000000000) (491835569039 / 500000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (491794029057 / 500000000000) (491835569039 / 500000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1347467510581 / 1000000000000) (67379963583 / 50000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1394526183 / 2000000000) (1394568417 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (30385988673 / 62500000000) (15193914607 / 31250000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169496227203 / 500000000000) (67804651013 / 200000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169496227203 / 500000000000) (67804651013 / 200000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (114195329661 / 250000000000) (228433745801 / 500000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (218881846133 / 100000000000) (2189231387503 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-8584574573 / 31250000000) (-136260020291 / 500000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-8584574573 / 31250000000) (-136260020291 / 500000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (90543 / 250000) (45387 / 125000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (20165315963 / 20000000000) (1008308379451 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (365165640647 / 1000000000000) (183056369673 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (365165640647 / 1000000000000) (183056369673 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (271629 / 1000000) (136161 / 500000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691517700051 / 1000000000000) (34578392413 / 50000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (72299486053 / 50000000000) (1446094582867 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (392772741941 / 1000000000000) (98450842249 / 250000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (392772741941 / 1000000000000) (98450842249 / 250000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-98450842249 / 250000000000) (-392772741941 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-28637728349 / 1000000000000) (-5332000519 / 200000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-28637728349 / 1000000000000) (-5332000519 / 200000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-59890169343 / 1000000000000) (-3483659253 / 62500000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-334596555679 / 1000000000000) (-32825858863 / 100000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1394526183 / 1000000000) (1394568417 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (90543 / 1000000) (45387 / 500000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (8198034849 / 1000000000000) (2059979769 / 250000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-2059979769 / 250000000000) (-8198034849 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (346571565981 / 250000000000) (1386370382151 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (346571565981 / 250000000000) (1386370382151 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (62759258597 / 500000000000) (12584638507 / 100000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (247940020231 / 250000000000) (991801965151 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (491794029057 / 500000000000) (491835569039 / 500000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (491794029057 / 500000000000) (491835569039 / 500000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1394526183 / 2000000000) (1394568417 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (30385988673 / 62500000000) (15193914607 / 31250000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (30385988673 / 62500000000) (15193914607 / 31250000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (119549182371 / 250000000000) (478266088747 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (522721568353 / 250000000000) (418237908519 / 200000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (262444944659 / 1000000000000) (16448040277 / 62500000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (262444944659 / 1000000000000) (16448040277 / 62500000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (1649597421 / 100000000000) (661897689 / 40000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (88189689691 / 125000000000) (14111799739 / 20000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (88189689691 / 125000000000) (14111799739 / 20000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (248877483769 / 500000000000) (99571445937 / 200000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (248877483769 / 500000000000) (99571445937 / 200000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-166581314273 / 1000000000000) (-163392343127 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2090718027889 / 500000000000) (209130307449 / 50000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (1649597421 / 100000000000) (661897689 / 40000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (88189689691 / 125000000000) (14111799739 / 20000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1475038192887 / 500000000000) (737801254519 / 250000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-182049127 / 2000000000) (-90791649 / 1000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (182329659 / 2000000000) (36600441 / 400000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (182329659 / 2000000000) (36600441 / 400000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (268943210721 / 1000000000000) (135019256429 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (199925579 / 1953125000) (106646169731 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (901 / 5000) (1803 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (811801 / 25000000) (3250809 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (811801 / 25000000) (3250809 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3250809 / 100000000) (-811801 / 25000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96749191 / 100000000) (24188199 / 25000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96749191 / 100000000) (24188199 / 25000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1033561862129 / 1000000000000) (516800186991 / 500000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1033561862129 / 1000000000000) (516800186991 / 500000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1033561862129 / 1000000000000) (516800186991 / 500000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (67813271427 / 250000000000) (136005604653 / 500000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (93403745539 / 250000000000) (378657379037 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (344510771659 / 500000000000) (27561701789 / 40000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (118687671789 / 250000000000) (237389814221 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (118687671789 / 250000000000) (237389814221 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (17737396951 / 100000000000) (179778809727 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477608158401 / 1000000000000) (477628983479 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2093675288957 / 1000000000000) (2093766579173 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (371363496867 / 1000000000000) (7528297269 / 20000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (371363496867 / 1000000000000) (7528297269 / 20000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (8909573135529087979805669 / 23402758834544040000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_302 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((901 / 5000):ℝ) ((1803 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (8909573135529087979805669 / 23402758834544040000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (900099 / 10000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1804803 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1803 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_302 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_302 {a z : ℝ}
    (ha : a ∈ Set.Icc ((901 / 5000):ℝ) ((1803 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_302 ha ⟨hz.1.le,hz.2⟩ hs) (M := (8909573135529087979805669 / 23402758834544040000000000))
  exact lt_of_lt_of_le (by norm_num : (8909573135529087979805669 / 23402758834544040000000000) < 2*((901 / 5000):ℝ)/(1-((901 / 5000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0303 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_303 (a z s c : ℝ)
    (ha : Bounds (1803 / 10000) (451 / 2500) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1801197 / 20000000) (451451 / 5000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (7131587202913418497029013069 / 18720811918308962000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(451 / 2500)
  have hx1 : Bounds (2951 / 2500) (2951 / 2500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((451 / 2500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(451 / 2500)
  have hx2 : Bounds (2951 / 2500) (2951 / 2500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((451 / 2500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (41463341 / 250000000) (33170673 / 200000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4213.1) (by simpa only [div_one] using reflection_log_4213.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (39154662173 / 200000000000) (97886656023 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(451 / 2500)
  have hx5 : Bounds (-451 / 2500) (-451 / 2500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((451 / 2500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2049 / 2500) (2049 / 2500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(451 / 2500)
  have hx7 : Bounds (2049 / 2500) (2049 / 2500) x7 := by
    exact hx6
  let x8 : ℝ := -(451 / 2500)
  have hx8 : Bounds (-451 / 2500) (-451 / 2500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((451 / 2500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (2049 / 2500) (2049 / 2500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(451 / 2500)
  have hx10 : Bounds (2049 / 2500) (2049 / 2500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-198938863 / 1000000000) (-99469431 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4214.1) (by simpa only [div_one] using reflection_log_4214.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-32610058423 / 200000000000) (-32610058259 / 200000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (5235683 / 160000000) (32723020751 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (5235683 / 320000000) (2045188797 / 125000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (5235683 / 320000000) (2045188797 / 125000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-2045188797 / 125000000000) (-5235683 / 320000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (84598208703 / 125000000000) (5414285373 / 8000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (84598208703 / 125000000000) (5414285373 / 8000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (451 / 2500)
  have hx20 : Bounds (84598208703 / 125000000000) (5414285373 / 8000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1803 / 10000)
  have hx22 : Bounds (11803 / 10000) (11803 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1803 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1803 / 10000)
  have hx23 : Bounds (11803 / 10000) (11803 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1803 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (165768643 / 1000000000) (41442161 / 250000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4199.1) (by simpa only [div_one] using reflection_log_4199.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (48914182333 / 250000000000) (97828365257 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1803 / 10000)
  have hx26 : Bounds (-1803 / 10000) (-1803 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1803 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8197 / 10000) (8197 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1803 / 10000)
  have hx28 : Bounds (8197 / 10000) (8197 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1803 / 10000)
  have hx29 : Bounds (-1803 / 10000) (-1803 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1803 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8197 / 10000) (8197 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1803 / 10000)
  have hx31 : Bounds (8197 / 10000) (8197 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-9940843 / 50000000) (-198816859 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4200.1) (by simpa only [div_one] using reflection_log_4200.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-81485090071 / 500000000000) (-81485089661 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (3268654919 / 100000000000) (4085818899 / 125000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (3268654919 / 200000000000) (4085818899 / 250000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (3268654919 / 200000000000) (4085818899 / 250000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-4085818899 / 250000000000) (-3268654919 / 200000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (169200976101 / 250000000000) (135360781281 / 200000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (169200976101 / 250000000000) (135360781281 / 200000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1803 / 10000)
  have hx41 : Bounds (169200976101 / 250000000000) (135360781281 / 200000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (84598208703 / 125000000000) (135360781281 / 200000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (451 / 2500000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(451 / 2500000)
  have hx45 : Bounds (2500451 / 2500000) (2500451 / 2500000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((451 / 2500000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(451 / 2500000)
  have hx46 : Bounds (2500451 / 2500000) (2500451 / 2500000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((451 / 2500000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (180383 / 1000000000) (5637 / 31250000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4215.1) (by simpa only [div_one] using reflection_log_4215.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (180415541 / 1000000000000) (90208271 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(451 / 2500000)
  have hx49 : Bounds (-451 / 2500000) (-451 / 2500000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((451 / 2500000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (2499549 / 2500000) (2499549 / 2500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(451 / 2500000)
  have hx51 : Bounds (2499549 / 2500000) (2499549 / 2500000) x51 := by
    exact hx50
  let x52 : ℝ := -(451 / 2500000)
  have hx52 : Bounds (-451 / 2500000) (-451 / 2500000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((451 / 2500000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (2499549 / 2500000) (2499549 / 2500000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(451 / 2500000)
  have hx54 : Bounds (2499549 / 2500000) (2499549 / 2500000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-180417 / 1000000000) (-2819 / 15625000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4216.1) (by simpa only [div_one] using reflection_log_4216.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-180384453 / 1000000000000) (-45095863 / 250000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (1943 / 62500000000) (3309 / 100000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (1943 / 125000000000) (3309 / 200000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (1943 / 125000000000) (3309 / 200000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-3309 / 200000000000) (-1943 / 125000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (138629432691 / 200000000000) (43321697841 / 62500000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (138629432691 / 200000000000) (43321697841 / 62500000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (451 / 2500000)
  have hx64 : Bounds (138629432691 / 200000000000) (43321697841 / 62500000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(0 / 1)
  have hx66 : Bounds (1 / 1) (1 / 1) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(0 / 1)
  have hx67 : Bounds (1 / 1) (1 / 1) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (0 / 1) (0 / 1) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (0 / 1) (0 / 1) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(0 / 1)
  have hx70 : Bounds (0 / 1) (0 / 1) x70 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1 / 1) (1 / 1) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(0 / 1)
  have hx72 : Bounds (1 / 1) (1 / 1) x72 := by
    exact hx71
  let x73 : ℝ := -(0 / 1)
  have hx73 : Bounds (0 / 1) (0 / 1) x73 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(0 / 1)
  have hx75 : Bounds (1 / 1) (1 / 1) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (0 / 1) (0 / 1) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (0 / 1) (0 / 1) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (0 / 1) (0 / 1) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (0 / 1)
  have hx85 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (138629432691 / 200000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1369932833079 / 1000000000000) (273990217481 / 200000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (684966416539 / 1000000000000) (684975543703 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (684966416539 / 1000000000000) (684975543703 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (5537699551003 / 500000000000) (1387965891571 / 125000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (94828455433 / 12500000000) (7605781529761 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (94828455433 / 12500000000) (7605781529761 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(90593 / 1000000)
  have hx95 : Bounds (1090593 / 1000000) (1090593 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90593 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(90593 / 1000000)
  have hx96 : Bounds (1090593 / 1000000) (1090593 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90593 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (17344317 / 200000000) (43360793 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4217.1) (by simpa only [div_one] using reflection_log_4217.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (94577953549 / 1000000000000) (94577954641 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(90593 / 1000000)
  have hx99 : Bounds (-90593 / 1000000) (-90593 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90593 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (909407 / 1000000) (909407 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(90593 / 1000000)
  have hx101 : Bounds (909407 / 1000000) (909407 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(90593 / 1000000)
  have hx102 : Bounds (-90593 / 1000000) (-90593 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90593 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (909407 / 1000000) (909407 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(90593 / 1000000)
  have hx104 : Bounds (909407 / 1000000) (909407 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-94962541 / 1000000000) (-4748127 / 50000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4218.1) (by simpa only [div_one] using reflection_log_4218.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-21589899881 / 250000000000) (-86359598613 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (328734161 / 40000000000) (2054589007 / 250000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (1027294253 / 250000000000) (2054589007 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (1027294253 / 250000000000) (2054589007 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2054589007 / 500000000000) (-1027294253 / 250000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (344519000993 / 500000000000) (172259500997 / 250000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (344519000993 / 500000000000) (172259500997 / 250000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (90593 / 1000000)
  have hx114 : Bounds (344519000993 / 500000000000) (172259500997 / 250000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(3633 / 40000)
  have hx116 : Bounds (43633 / 40000) (43633 / 40000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3633 / 40000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(3633 / 40000)
  have hx117 : Bounds (43633 / 40000) (43633 / 40000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3633 / 40000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (8693429 / 100000000) (86934291 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4219.1) (by simpa only [div_one] using reflection_log_4219.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (94830096889 / 1000000000000) (94830097981 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(3633 / 40000)
  have hx120 : Bounds (-3633 / 40000) (-3633 / 40000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3633 / 40000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (36367 / 40000) (36367 / 40000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(3633 / 40000)
  have hx122 : Bounds (36367 / 40000) (36367 / 40000) x122 := by
    exact hx121
  let x123 : ℝ := -(3633 / 40000)
  have hx123 : Bounds (-3633 / 40000) (-3633 / 40000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3633 / 40000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (36367 / 40000) (36367 / 40000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(3633 / 40000)
  have hx125 : Bounds (36367 / 40000) (36367 / 40000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-19043537 / 200000000) (-23804421 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4220.1) (by simpa only [div_one] using reflection_log_4220.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-2164238469 / 25000000000) (-1731390757 / 20000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (8260558129 / 1000000000000) (8260560131 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (516284883 / 125000000000) (2065140033 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (516284883 / 125000000000) (2065140033 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2065140033 / 500000000000) (-516284883 / 125000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (344508449967 / 500000000000) (43063556371 / 62500000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (344508449967 / 500000000000) (43063556371 / 62500000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (3633 / 40000)
  have hx135 : Bounds (344508449967 / 500000000000) (43063556371 / 62500000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(90593 / 1000000)
  have hx136 : Bounds (687263541043 / 1000000000000) (344515283063 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((90593 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(3633 / 40000)
  have hx137 : Bounds (86127944647 / 125000000000) (690795107441 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((3633 / 40000) : ℝ)) <;> norm_num
  have hc : Bounds (90593 / 1000000) (3633 / 40000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(90593 / 1000000) ≤ (344515283063 / 500000000000) := hx136.2
      have h2 : (344519000993 / 500000000000) ≤ biasE (90593 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (3633 / 40000) ≤ (43063556371 / 62500000000) := hx135.2
      have h2 : (86127944647 / 125000000000) ≤ x93*(3633 / 40000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(3633 / 40000)
  have hx139 : Bounds (43633 / 40000) (43633 / 40000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3633 / 40000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(3633 / 40000)
  have hx140 : Bounds (43633 / 40000) (43633 / 40000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3633 / 40000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (8693429 / 100000000) (86934291 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4219.1) (by simpa only [div_one] using reflection_log_4219.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (94830096889 / 1000000000000) (94830097981 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(3633 / 40000)
  have hx143 : Bounds (-3633 / 40000) (-3633 / 40000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3633 / 40000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (36367 / 40000) (36367 / 40000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(3633 / 40000)
  have hx145 : Bounds (36367 / 40000) (36367 / 40000) x145 := by
    exact hx144
  let x146 : ℝ := -(3633 / 40000)
  have hx146 : Bounds (-3633 / 40000) (-3633 / 40000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3633 / 40000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (36367 / 40000) (36367 / 40000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(3633 / 40000)
  have hx148 : Bounds (36367 / 40000) (36367 / 40000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-19043537 / 200000000) (-23804421 / 250000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4220.1) (by simpa only [div_one] using reflection_log_4220.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-2164238469 / 25000000000) (-1731390757 / 20000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (8260558129 / 1000000000000) (8260560131 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (516284883 / 125000000000) (2065140033 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (516284883 / 125000000000) (2065140033 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-2065140033 / 500000000000) (-516284883 / 125000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (344508449967 / 500000000000) (43063556371 / 62500000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (344508449967 / 500000000000) (43063556371 / 62500000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (3633 / 40000)
  have hx158 : Bounds (344508449967 / 500000000000) (43063556371 / 62500000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(90593 / 1000000)
  have hx160 : Bounds (1090593 / 1000000) (1090593 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90593 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(90593 / 1000000)
  have hx161 : Bounds (1090593 / 1000000) (1090593 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((90593 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (17344317 / 200000000) (43360793 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4217.1) (by simpa only [div_one] using reflection_log_4217.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (94577953549 / 1000000000000) (94577954641 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(90593 / 1000000)
  have hx164 : Bounds (-90593 / 1000000) (-90593 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90593 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (909407 / 1000000) (909407 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(90593 / 1000000)
  have hx166 : Bounds (909407 / 1000000) (909407 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(90593 / 1000000)
  have hx167 : Bounds (-90593 / 1000000) (-90593 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((90593 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (909407 / 1000000) (909407 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(90593 / 1000000)
  have hx169 : Bounds (909407 / 1000000) (909407 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-94962541 / 1000000000) (-4748127 / 50000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4218.1) (by simpa only [div_one] using reflection_log_4218.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-21589899881 / 250000000000) (-86359598613 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (328734161 / 40000000000) (2054589007 / 250000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (1027294253 / 250000000000) (2054589007 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (1027294253 / 250000000000) (2054589007 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-2054589007 / 500000000000) (-1027294253 / 250000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (344519000993 / 500000000000) (172259500997 / 250000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (344519000993 / 500000000000) (172259500997 / 250000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (90593 / 1000000)
  have hx179 : Bounds (344519000993 / 500000000000) (172259500997 / 250000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (344508449967 / 500000000000) (172259500997 / 250000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-13198689 / 1600000000) (-8207091649 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4141697 / 500000000) (-1648191 / 200000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4221.1) (by simpa only [div_one] using reflection_log_4222.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4141697 / 1000000000) (-1648191 / 400000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4141697 / 1000000000) (-1648191 / 400000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (1648191 / 400000000) (4141697 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (278907063 / 400000000) (348644439 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (278907063 / 400000000) (348644439 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (90593 / 1000000) (3633 / 40000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-13198689 / 1600000000) (-8207091649 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1090593 / 1000000) (43633 / 40000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-3633 / 40000) (-90593 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (36367 / 40000) (909407 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (36367 / 40000) (909407 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (549808831469 / 500000000000) (274974564853 / 250000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (299808831469 / 250000000000) (149974564853 / 125000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (299808831469 / 250000000000) (149974564853 / 125000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (1453473 / 8000000) (7286079 / 40000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4223.1) (by simpa only [div_one] using reflection_log_4224.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (1453473 / 16000000) (7286079 / 80000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (1453473 / 16000000) (7286079 / 80000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11803 / 10000) (2951 / 2500) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-451 / 2500) (-1803 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (2049 / 2500) (8197 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (2049 / 2500) (8197 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (121995852141 / 100000000000) (1220107369449 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (71995852141 / 50000000000) (720107369449 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (71995852141 / 50000000000) (720107369449 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (182292751 / 500000000) (364792227 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4225.1) (by simpa only [div_one] using reflection_log_4226.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (182292751 / 1000000000) (364792227 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (182292751 / 1000000000) (364792227 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (278907063 / 200000000) (348644439 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (90593 / 1000000) (3633 / 40000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-13198689 / 1600000000) (-8207091649 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (443611563 / 320000000) (1386370664351 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (443611563 / 320000000) (1386370664351 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (119396821841 / 125000000000) (119407759419 / 125000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (684966416539 / 500000000000) (684975543703 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (98356968773 / 100000000000) (15369580829 / 15625000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (98356968773 / 100000000000) (15369580829 / 15625000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1347424408841 / 1000000000000) (1347556734059 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (278907063 / 400000000) (348644439 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (97236437239 / 200000000000) (486211779383 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169499557043 / 500000000000) (339030066117 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169499557043 / 500000000000) (339030066117 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (228387840447 / 500000000000) (91372449729 / 200000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1094421790119 / 500000000000) (273657301009 / 125000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2090727735899 / 1000000000000) (2091315530377 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2090727735899 / 1000000000000) (2091315530377 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-7286079 / 80000000) (-1453473 / 16000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (278907063 / 200000000) (348644439 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (90593 / 1000000) (3633 / 40000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-13198689 / 1600000000) (-8207091649 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (443611563 / 320000000) (1386370664351 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (443611563 / 320000000) (1386370664351 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-126265077297 / 1000000000000) (-125933091661 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (15754296959 / 15625000000) (126039724453 / 125000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (45671328781 / 500000000000) (22895115947 / 250000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (45671328781 / 500000000000) (22895115947 / 250000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (45671328781 / 250000000000) (22895115947 / 125000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (90593 / 500000) (3633 / 20000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-3633 / 20000) (-90593 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (258828781 / 250000000000) (246865947 / 125000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (258828781 / 250000000000) (246865947 / 125000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (713349617 / 1000000000000) (272160031 / 200000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-392349149 / 3125000000) (-62286145753 / 500000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (684966416539 / 500000000000) (684975543703 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (98356968773 / 100000000000) (15369580829 / 15625000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (98356968773 / 100000000000) (15369580829 / 15625000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1347424408841 / 1000000000000) (1347556734059 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (278907063 / 400000000) (348644439 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (97236437239 / 200000000000) (486211779383 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169499557043 / 500000000000) (339030066117 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169499557043 / 500000000000) (339030066117 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (228387840447 / 500000000000) (91372449729 / 200000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1094421790119 / 500000000000) (273657301009 / 125000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-17179073467 / 62500000000) (-136334630269 / 500000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-17179073467 / 62500000000) (-136334630269 / 500000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (90593 / 250000) (3633 / 10000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (15754296959 / 15625000000) (126039724453 / 125000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (45671328781 / 125000000000) (366321855151 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (45671328781 / 125000000000) (366321855151 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (271779 / 1000000) (10899 / 40000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691515770649 / 1000000000000) (691566164273 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (722996621047 / 500000000000) (1446098617623 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (392990597343 / 1000000000000) (394025720837 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (392990597343 / 1000000000000) (394025720837 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-394025720837 / 1000000000000) (-392990597343 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-28655090589 / 1000000000000) (-1666796387 / 62500000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-28655090589 / 1000000000000) (-1666796387 / 62500000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-29963417987 / 500000000000) (-27878539491 / 500000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-167396005723 / 500000000000) (-1026332311 / 3125000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (278907063 / 200000000) (348644439 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (90593 / 1000000) (3633 / 40000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (8207091649 / 1000000000000) (13198689 / 1600000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-13198689 / 1600000000) (-8207091649 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (443611563 / 320000000) (1386370664351 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (443611563 / 320000000) (1386370664351 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (125587819771 / 1000000000000) (12591711559 / 100000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (1586801311 / 1600000000) (991792908351 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (98356968773 / 100000000000) (15369580829 / 15625000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (98356968773 / 100000000000) (15369580829 / 15625000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (278907063 / 400000000) (348644439 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (97236437239 / 200000000000) (486211779383 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (97236437239 / 200000000000) (486211779383 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (95638812211 / 200000000000) (29891484973 / 62500000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2090896456179 / 1000000000000) (2091201211897 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (131295563649 / 500000000000) (263318024721 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (131295563649 / 500000000000) (263318024721 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (16514447191 / 1000000000000) (16566127009 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (5644250777 / 8000000000) (705604130997 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (5644250777 / 8000000000) (705604130997 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (31110905111 / 62500000000) (497877189681 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (31110905111 / 62500000000) (497877189681 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-166685305787 / 1000000000000) (-40870562739 / 250000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2090727735899 / 500000000000) (2091315530377 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (16514447191 / 1000000000000) (16566127009 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (5644250777 / 8000000000) (705604130997 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (73753697799 / 25000000000) (590256350981 / 200000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-7286079 / 80000000) (-1453473 / 16000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (182433527 / 2000000000) (91554051 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (182433527 / 2000000000) (91554051 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (430564711 / 1600000000) (16887612519 / 62500000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (25604409647 / 250000000000) (26679887337 / 250000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1803 / 10000) (451 / 2500) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3250809 / 100000000) (203401 / 6250000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3250809 / 100000000) (203401 / 6250000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-203401 / 6250000) (-3250809 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (6046599 / 6250000) (96749191 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (6046599 / 6250000) (96749191 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1033600373981 / 1000000000000) (129204863759 / 125000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1033600373981 / 1000000000000) (129204863759 / 125000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1033600373981 / 1000000000000) (129204863759 / 125000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (271414287379 / 1000000000000) (10887030243 / 40000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (373831925967 / 1000000000000) (378895305423 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (344508449967 / 500000000000) (172259500997 / 250000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (237372144197 / 500000000000) (23738668547 / 50000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (237372144197 / 500000000000) (23738668547 / 50000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (22184321459 / 125000000000) (17988940139 / 100000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (238802464363 / 500000000000) (477625828327 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (1046844559791 / 500000000000) (2093780737707 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (2902942029 / 7812500000) (376648963549 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (2902942029 / 7812500000) (376648963549 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (7131587202913418497029013069 / 18720811918308962000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_303 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1803 / 10000):ℝ) ((451 / 2500)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (7131587202913418497029013069 / 18720811918308962000000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (1801197 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (451451 / 5000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (451 / 2500))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_303 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_303 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1803 / 10000):ℝ) ((451 / 2500)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_303 ha ⟨hz.1.le,hz.2⟩ hs) (M := (7131587202913418497029013069 / 18720811918308962000000000000))
  exact lt_of_lt_of_le (by norm_num : (7131587202913418497029013069 / 18720811918308962000000000000) < 2*((1803 / 10000):ℝ)/(1-((1803 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end


