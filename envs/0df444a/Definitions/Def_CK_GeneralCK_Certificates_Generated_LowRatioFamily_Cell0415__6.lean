-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0415__6
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0415__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:39:04.705882+00:00
-- url     : https://prove2.me/theorems/08466d85-9e73-4ed3-ad7d-ae37ccf9c650
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0415 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0416, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0415 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0416, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0417, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0418, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0419, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0420)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0415 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0416, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0417, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0418, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0419, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0420)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0415 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0416, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0417, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0418, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0419, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0420) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0415 (+5 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0416, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0417, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0418, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0419, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0420).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0090__2

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0415 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_415 (a z s c : ℝ)
    (ha : Bounds (383 / 2000) (479 / 2500) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (382617 / 4000000) (479479 / 5000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (6047854004883501510031579 / 14848005662721000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(479 / 2500)
  have hx1 : Bounds (2979 / 2500) (2979 / 2500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((479 / 2500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(479 / 2500)
  have hx2 : Bounds (2979 / 2500) (2979 / 2500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((479 / 2500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (175296941 / 1000000000) (87648471 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_5780.1) (by simpa only [div_one] using reflection_log_5780.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (41776766979 / 200000000000) (26110479511 / 125000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(479 / 2500)
  have hx5 : Bounds (-479 / 2500) (-479 / 2500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((479 / 2500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2021 / 2500) (2021 / 2500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(479 / 2500)
  have hx7 : Bounds (2021 / 2500) (2021 / 2500) x7 := by
    exact hx6
  let x8 : ℝ := -(479 / 2500)
  have hx8 : Bounds (-479 / 2500) (-479 / 2500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((479 / 2500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (2021 / 2500) (2021 / 2500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(479 / 2500)
  have hx10 : Bounds (2021 / 2500) (2021 / 2500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-106349147 / 500000000) (-212698293 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_5781.1) (by simpa only [div_one] using reflection_log_5781.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-17194530087 / 100000000000) (-171945300061 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (1477541361 / 40000000000) (36938536027 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (4617316753 / 250000000000) (9234634007 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (4617316753 / 250000000000) (9234634007 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-9234634007 / 500000000000) (-4617316753 / 250000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (337338955993 / 500000000000) (168669478497 / 250000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (337338955993 / 500000000000) (168669478497 / 250000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (479 / 2500)
  have hx20 : Bounds (337338955993 / 500000000000) (168669478497 / 250000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(383 / 2000)
  have hx22 : Bounds (2383 / 2000) (2383 / 2000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((383 / 2000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(383 / 2000)
  have hx23 : Bounds (2383 / 2000) (2383 / 2000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((383 / 2000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (175213017 / 1000000000) (87606509 / 500000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_5766.1) (by simpa only [div_one] using reflection_log_5766.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (41753261951 / 200000000000) (208766310947 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(383 / 2000)
  have hx26 : Bounds (-383 / 2000) (-383 / 2000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((383 / 2000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (1617 / 2000) (1617 / 2000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(383 / 2000)
  have hx28 : Bounds (1617 / 2000) (1617 / 2000) x28 := by
    exact hx27
  let x29 : ℝ := -(383 / 2000)
  have hx29 : Bounds (-383 / 2000) (-383 / 2000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((383 / 2000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (1617 / 2000) (1617 / 2000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(383 / 2000)
  have hx31 : Bounds (1617 / 2000) (1617 / 2000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-1062873 / 5000000) (-212574599 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_5767.1) (by simpa only [div_one] using reflection_log_5767.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-1718665641 / 10000000000) (-171866563291 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (7379949131 / 200000000000) (4612468457 / 125000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (18449872827 / 1000000000000) (4612468457 / 250000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (18449872827 / 1000000000000) (4612468457 / 250000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-4612468457 / 250000000000) (-18449872827 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (168674326543 / 250000000000) (674697308173 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (168674326543 / 250000000000) (674697308173 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (383 / 2000)
  have hx41 : Bounds (168674326543 / 250000000000) (674697308173 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (337338955993 / 500000000000) (674697308173 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (479 / 2500000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(479 / 2500000)
  have hx45 : Bounds (2500479 / 2500000) (2500479 / 2500000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((479 / 2500000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(479 / 2500000)
  have hx46 : Bounds (2500479 / 2500000) (2500479 / 2500000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((479 / 2500000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (191581 / 1000000000) (95791 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5782.1) (by simpa only [div_one] using reflection_log_5782.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (95808853 / 500000000000) (47904677 / 250000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(479 / 2500000)
  have hx49 : Bounds (-479 / 2500000) (-479 / 2500000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((479 / 2500000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (2499521 / 2500000) (2499521 / 2500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(479 / 2500000)
  have hx51 : Bounds (2499521 / 2500000) (2499521 / 2500000) x51 := by
    exact hx50
  let x52 : ℝ := -(479 / 2500000)
  have hx52 : Bounds (-479 / 2500000) (-479 / 2500000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((479 / 2500000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (2499521 / 2500000) (2499521 / 2500000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(479 / 2500000)
  have hx54 : Bounds (2499521 / 2500000) (2499521 / 2500000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-191619 / 1000000000) (-95809 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_5783.1) (by simpa only [div_one] using reflection_log_5783.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-95791143 / 500000000000) (-38316257 / 200000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (1771 / 50000000000) (37423 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (1771 / 100000000000) (2339 / 125000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (1771 / 100000000000) (2339 / 125000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-2339 / 125000000000) (-1771 / 100000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (86643395161 / 125000000000) (69314716329 / 100000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (86643395161 / 125000000000) (69314716329 / 100000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (479 / 2500000)
  have hx64 : Bounds (86643395161 / 125000000000) (69314716329 / 100000000000) x64 := by
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
  have hx86 : Bounds (86643395161 / 125000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (683912536637 / 500000000000) (1367844489173 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (683912536637 / 1000000000000) (683922244587 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (683912536637 / 1000000000000) (683922244587 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (10427985375793 / 1000000000000) (5227159274157 / 500000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (1782957482593 / 250000000000) (7149941007191 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (1782957482593 / 250000000000) (7149941007191 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(19259 / 200000)
  have hx95 : Bounds (219259 / 200000) (219259 / 200000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19259 / 200000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(19259 / 200000)
  have hx96 : Bounds (219259 / 200000) (219259 / 200000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19259 / 200000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (11492039 / 125000000) (91936313 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_5784.1) (by simpa only [div_one] using reflection_log_5784.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (25197329791 / 250000000000) (100789320261 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(19259 / 200000)
  have hx99 : Bounds (-19259 / 200000) (-19259 / 200000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19259 / 200000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (180741 / 200000) (180741 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(19259 / 200000)
  have hx101 : Bounds (180741 / 200000) (180741 / 200000) x101 := by
    exact hx100
  let x102 : ℝ := -(19259 / 200000)
  have hx102 : Bounds (-19259 / 200000) (-19259 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19259 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (180741 / 200000) (180741 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(19259 / 200000)
  have hx104 : Bounds (180741 / 200000) (180741 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-1012523 / 10000000) (-101252299 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_5785.1) (by simpa only [div_one] using reflection_log_5785.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-22875552443 / 250000000000) (-91502208867 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (580444337 / 62500000000) (4643555697 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (580444337 / 125000000000) (4643555697 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (580444337 / 125000000000) (4643555697 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4643555697 / 1000000000000) (-580444337 / 125000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688503624303 / 1000000000000) (10757869161 / 15625000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688503624303 / 1000000000000) (10757869161 / 15625000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (19259 / 200000)
  have hx114 : Bounds (688503624303 / 1000000000000) (10757869161 / 15625000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(96537 / 1000000)
  have hx116 : Bounds (1096537 / 1000000) (1096537 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96537 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(96537 / 1000000)
  have hx117 : Bounds (1096537 / 1000000) (1096537 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96537 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (11519629 / 125000000) (92157033 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_5786.1) (by simpa only [div_one] using reflection_log_5786.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (50526797699 / 500000000000) (20210719299 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(96537 / 1000000)
  have hx120 : Bounds (-96537 / 1000000) (-96537 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96537 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (903463 / 1000000) (903463 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(96537 / 1000000)
  have hx122 : Bounds (903463 / 1000000) (903463 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(96537 / 1000000)
  have hx123 : Bounds (-96537 / 1000000) (-96537 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96537 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (903463 / 1000000) (903463 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(96537 / 1000000)
  have hx125 : Bounds (903463 / 1000000) (903463 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-50760061 / 500000000) (-101520121 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_5787.1) (by simpa only [div_one] using reflection_log_5787.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-91719673983 / 1000000000000) (-91719673079 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (1866784283 / 200000000000) (1166740427 / 125000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4666960707 / 1000000000000) (1166740427 / 250000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4666960707 / 1000000000000) (1166740427 / 250000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-1166740427 / 250000000000) (-4666960707 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (172120054573 / 250000000000) (688480220293 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (172120054573 / 250000000000) (688480220293 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (96537 / 1000000)
  have hx135 : Bounds (172120054573 / 250000000000) (688480220293 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(19259 / 200000)
  have hx136 : Bounds (137351912629 / 200000000000) (86062946161 / 125000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((19259 / 200000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(96537 / 1000000)
  have hx137 : Bounds (172121366497 / 250000000000) (172558463753 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((96537 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (19259 / 200000) (96537 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(19259 / 200000) ≤ (86062946161 / 125000000000) := hx136.2
      have h2 : (688503624303 / 1000000000000) ≤ biasE (19259 / 200000) := hx114.1
      linarith
    · have h1 : biasE (96537 / 1000000) ≤ (688480220293 / 1000000000000) := hx135.2
      have h2 : (172121366497 / 250000000000) ≤ x93*(96537 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(96537 / 1000000)
  have hx139 : Bounds (1096537 / 1000000) (1096537 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96537 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(96537 / 1000000)
  have hx140 : Bounds (1096537 / 1000000) (1096537 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96537 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (11519629 / 125000000) (92157033 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_5786.1) (by simpa only [div_one] using reflection_log_5786.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (50526797699 / 500000000000) (20210719299 / 200000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(96537 / 1000000)
  have hx143 : Bounds (-96537 / 1000000) (-96537 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96537 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (903463 / 1000000) (903463 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(96537 / 1000000)
  have hx145 : Bounds (903463 / 1000000) (903463 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(96537 / 1000000)
  have hx146 : Bounds (-96537 / 1000000) (-96537 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96537 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (903463 / 1000000) (903463 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(96537 / 1000000)
  have hx148 : Bounds (903463 / 1000000) (903463 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-50760061 / 500000000) (-101520121 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_5787.1) (by simpa only [div_one] using reflection_log_5787.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-91719673983 / 1000000000000) (-91719673079 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (1866784283 / 200000000000) (1166740427 / 125000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4666960707 / 1000000000000) (1166740427 / 250000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4666960707 / 1000000000000) (1166740427 / 250000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-1166740427 / 250000000000) (-4666960707 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (172120054573 / 250000000000) (688480220293 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (172120054573 / 250000000000) (688480220293 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (96537 / 1000000)
  have hx158 : Bounds (172120054573 / 250000000000) (688480220293 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(19259 / 200000)
  have hx160 : Bounds (219259 / 200000) (219259 / 200000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19259 / 200000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(19259 / 200000)
  have hx161 : Bounds (219259 / 200000) (219259 / 200000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19259 / 200000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (11492039 / 125000000) (91936313 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_5784.1) (by simpa only [div_one] using reflection_log_5784.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (25197329791 / 250000000000) (100789320261 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(19259 / 200000)
  have hx164 : Bounds (-19259 / 200000) (-19259 / 200000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19259 / 200000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (180741 / 200000) (180741 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(19259 / 200000)
  have hx166 : Bounds (180741 / 200000) (180741 / 200000) x166 := by
    exact hx165
  let x167 : ℝ := -(19259 / 200000)
  have hx167 : Bounds (-19259 / 200000) (-19259 / 200000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19259 / 200000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (180741 / 200000) (180741 / 200000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(19259 / 200000)
  have hx169 : Bounds (180741 / 200000) (180741 / 200000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-1012523 / 10000000) (-101252299 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_5785.1) (by simpa only [div_one] using reflection_log_5785.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-22875552443 / 250000000000) (-91502208867 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (580444337 / 62500000000) (4643555697 / 500000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (580444337 / 125000000000) (4643555697 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (580444337 / 125000000000) (4643555697 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4643555697 / 1000000000000) (-580444337 / 125000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688503624303 / 1000000000000) (10757869161 / 15625000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688503624303 / 1000000000000) (10757869161 / 15625000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (19259 / 200000)
  have hx179 : Bounds (688503624303 / 1000000000000) (10757869161 / 15625000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (172120054573 / 250000000000) (10757869161 / 15625000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-9319392369 / 1000000000000) (-370909081 / 40000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-936309 / 100000000) (-4657993 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_5788.1) (by simpa only [div_one] using reflection_log_5789.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-936309 / 200000000) (-4657993 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-936309 / 200000000) (-4657993 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (4657993 / 1000000000) (936309 / 200000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (697805173 / 1000000000) (348914363 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (697805173 / 1000000000) (348914363 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (19259 / 200000) (96537 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-9319392369 / 1000000000000) (-370909081 / 40000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (219259 / 200000) (1096537 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-96537 / 1000000) (-19259 / 200000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (903463 / 1000000) (180741 / 200000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (903463 / 1000000) (180741 / 200000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (69159736861 / 62500000000) (276713047463 / 250000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (37909736861 / 31250000000) (151713047463 / 125000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (37909736861 / 31250000000) (151713047463 / 125000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (48297153 / 250000000) (96838577 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_5790.1) (by simpa only [div_one] using reflection_log_5791.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (48297153 / 500000000) (96838577 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (48297153 / 500000000) (96838577 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (2383 / 2000) (2979 / 2500) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-479 / 2500) (-383 / 2000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (2021 / 2500) (1617 / 2000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (2021 / 2500) (1617 / 2000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (247371675943 / 200000000000) (247402276101 / 200000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (147371675943 / 100000000000) (147402276101 / 100000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (147371675943 / 100000000000) (147402276101 / 100000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (387787617 / 1000000000) (96998809 / 250000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_5792.1) (by simpa only [div_one] using reflection_log_5793.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (387787617 / 2000000000) (96998809 / 500000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (387787617 / 2000000000) (96998809 / 500000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (697805173 / 500000000) (348914363 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (19259 / 200000) (96537 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-9319392369 / 1000000000000) (-370909081 / 40000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386290953631 / 1000000000000) (55455388999 / 40000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386290953631 / 1000000000000) (55455388999 / 40000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (238608474593 / 250000000000) (477265455299 / 500000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (683912536637 / 500000000000) (683922244587 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (30670252073 / 31250000000) (981540529417 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (30670252073 / 31250000000) (981540529417 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (5369797093 / 4000000000) (41956087627 / 31250000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (697805173 / 1000000000) (348914363 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (97386411893 / 200000000000) (486964930831 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169891854997 / 500000000000) (339818117289 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169891854997 / 500000000000) (339818117289 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456142394543 / 1000000000000) (2281190193 / 5000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2191838284831 / 1000000000000) (2192297870059 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (261495594849 / 125000000000) (209261608221 / 100000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (261495594849 / 125000000000) (209261608221 / 100000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-96838577 / 1000000000) (-48297153 / 500000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (697805173 / 500000000) (348914363 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (19259 / 200000) (96537 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-9319392369 / 1000000000000) (-370909081 / 40000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386290953631 / 1000000000000) (55455388999 / 40000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386290953631 / 1000000000000) (55455388999 / 40000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-67127761971 / 500000000000) (-6695390629 / 50000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (201871903051 / 200000000000) (1009407060457 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (97196274521 / 1000000000000) (24361282349 / 250000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (97196274521 / 1000000000000) (24361282349 / 250000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (97196274521 / 500000000000) (24361282349 / 125000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (19259 / 100000) (96537 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-96537 / 500000) (-19259 / 100000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (659274521 / 500000000000) (287532349 / 125000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (659274521 / 500000000000) (287532349 / 125000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (226948733 / 250000000000) (39593413 / 25000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-13334772901 / 100000000000) (-6616203803 / 50000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (683912536637 / 500000000000) (683922244587 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (30670252073 / 31250000000) (981540529417 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (30670252073 / 31250000000) (981540529417 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (5369797093 / 4000000000) (41956087627 / 31250000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (697805173 / 1000000000) (348914363 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (97386411893 / 200000000000) (486964930831 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169891854997 / 500000000000) (339818117289 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169891854997 / 500000000000) (339818117289 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456142394543 / 1000000000000) (2281190193 / 5000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2191838284831 / 1000000000000) (2192297870059 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-146168971143 / 500000000000) (-290032975913 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-146168971143 / 500000000000) (-290032975913 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (19259 / 50000) (96537 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (201871903051 / 200000000000) (1009407060457 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (77757019617 / 200000000000) (194890258791 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (77757019617 / 200000000000) (194890258791 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (57777 / 200000) (289611 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (138260410559 / 200000000000) (345678975357 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (7232143631 / 5000000000) (1446545682827 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (52231445321 / 125000000000) (1675742167 / 4000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (52231445321 / 125000000000) (1675742167 / 4000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-1675742167 / 4000000000) (-52231445321 / 125000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-6030088733 / 200000000000) (-14035522493 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-6030088733 / 200000000000) (-14035522493 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-630933033 / 10000000000) (-58723636853 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-177715622793 / 500000000000) (-174378306383 / 500000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (697805173 / 500000000) (348914363 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (19259 / 200000) (96537 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (370909081 / 40000000000) (9319392369 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-9319392369 / 1000000000000) (-370909081 / 40000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386290953631 / 1000000000000) (55455388999 / 40000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386290953631 / 1000000000000) (55455388999 / 40000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (133492887379 / 1000000000000) (26767484439 / 200000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (990680607631 / 1000000000000) (39629090919 / 40000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (30670252073 / 31250000000) (981540529417 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (30670252073 / 31250000000) (981540529417 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (697805173 / 1000000000) (348914363 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (97386411893 / 200000000000) (486964930831 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (97386411893 / 200000000000) (486964930831 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (238949264099 / 500000000000) (29873488501 / 62500000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (261519507497 / 125000000000) (523123603127 / 250000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (279287953293 / 1000000000000) (17503378633 / 62500000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (279287953293 / 1000000000000) (17503378633 / 62500000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (18671004289 / 1000000000000) (18727948049 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (707151222581 / 1000000000000) (707231574353 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (707151222581 / 1000000000000) (707231574353 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (500062851597 / 1000000000000) (250088249881 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (500062851597 / 1000000000000) (250088249881 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-44444589081 / 250000000000) (-174400226293 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (261495594849 / 62500000000) (209261608221 / 50000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (18671004289 / 1000000000000) (18727948049 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (707151222581 / 1000000000000) (707231574353 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (184916929597 / 62500000000) (739982083169 / 250000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-96838577 / 1000000000) (-48297153 / 500000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (194110463 / 2000000000) (6087707 / 62500000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (194110463 / 2000000000) (6087707 / 62500000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (71788621641 / 250000000000) (144153411443 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (341800407 / 3125000000) (113906596593 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (383 / 2000) (479 / 2500) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (146689 / 4000000) (229441 / 6250000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (146689 / 4000000) (229441 / 6250000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-229441 / 6250000) (-146689 / 4000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (6020559 / 6250000) (3853311 / 4000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (6020559 / 6250000) (3853311 / 4000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (519034150111 / 500000000000) (1038109584177 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (519034150111 / 500000000000) (1038109584177 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (519034150111 / 500000000000) (1038109584177 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (289919970947 / 1000000000000) (290726801831 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (399296101187 / 1000000000000) (50579174803 / 125000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (172120054573 / 250000000000) (10757869161 / 15625000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (474005010979 / 1000000000000) (237018621717 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (474005010979 / 1000000000000) (237018621717 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (189268352827 / 1000000000000) (191811300791 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (59654713243 / 125000000000) (29828786789 / 62500000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (32738927899 / 15625000000) (523847962737 / 250000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (396572349233 / 1000000000000) (200959918299 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (396572349233 / 1000000000000) (200959918299 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (6047854004883501510031579 / 14848005662721000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_415 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((383 / 2000):ℝ) ((479 / 2500)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (6047854004883501510031579 / 14848005662721000000000000) := by
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
  have hsl : (382617 / 4000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (479479 / 5000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (479 / 2500))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_415 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_415 {a z : ℝ}
    (ha : a ∈ Set.Icc ((383 / 2000):ℝ) ((479 / 2500)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_415 ha ⟨hz.1.le,hz.2⟩ hs) (M := (6047854004883501510031579 / 14848005662721000000000000))
  exact lt_of_lt_of_le (by norm_num : (6047854004883501510031579 / 14848005662721000000000000) < 2*((383 / 2000):ℝ)/(1-((383 / 2000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0416 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_416 (a z s c : ℝ)
    (ha : Bounds (479 / 2500) (1917 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (478521 / 5000000) (1918917 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (14772902699052578175646997 / 36247130672481000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1917 / 10000)
  have hx1 : Bounds (11917 / 10000) (11917 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1917 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1917 / 10000)
  have hx2 : Bounds (11917 / 10000) (11917 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1917 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (175380859 / 1000000000) (8769043 / 50000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_5794.1) (by simpa only [div_one] using reflection_log_5794.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (20900136967 / 100000000000) (104500685431 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1917 / 10000)
  have hx5 : Bounds (-1917 / 10000) (-1917 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1917 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8083 / 10000) (8083 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1917 / 10000)
  have hx7 : Bounds (8083 / 10000) (8083 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1917 / 10000)
  have hx8 : Bounds (-1917 / 10000) (-1917 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1917 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8083 / 10000) (8083 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1917 / 10000)
  have hx10 : Bounds (8083 / 10000) (8083 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-212822003 / 1000000000) (-106411001 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_5795.1) (by simpa only [div_one] using reflection_log_5795.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-6880961001 / 40000000000) (-21503003027 / 125000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (7395468929 / 200000000000) (18488673323 / 500000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (9244336161 / 500000000000) (18488673323 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (9244336161 / 500000000000) (18488673323 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18488673323 / 1000000000000) (-9244336161 / 500000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674658506677 / 1000000000000) (337329254339 / 500000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674658506677 / 1000000000000) (337329254339 / 500000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1917 / 10000)
  have hx20 : Bounds (674658506677 / 1000000000000) (337329254339 / 500000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(479 / 2500)
  have hx22 : Bounds (2979 / 2500) (2979 / 2500) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((479 / 2500) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(479 / 2500)
  have hx23 : Bounds (2979 / 2500) (2979 / 2500) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((479 / 2500) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (175296941 / 1000000000) (87648471 / 500000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_5780.1) (by simpa only [div_one] using reflection_log_5780.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (41776766979 / 200000000000) (26110479511 / 125000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(479 / 2500)
  have hx26 : Bounds (-479 / 2500) (-479 / 2500) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((479 / 2500) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (2021 / 2500) (2021 / 2500) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(479 / 2500)
  have hx28 : Bounds (2021 / 2500) (2021 / 2500) x28 := by
    exact hx27
  let x29 : ℝ := -(479 / 2500)
  have hx29 : Bounds (-479 / 2500) (-479 / 2500) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((479 / 2500) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (2021 / 2500) (2021 / 2500) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(479 / 2500)
  have hx31 : Bounds (2021 / 2500) (2021 / 2500) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-106349147 / 500000000) (-212698293 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_5781.1) (by simpa only [div_one] using reflection_log_5781.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-17194530087 / 100000000000) (-171945300061 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (1477541361 / 40000000000) (36938536027 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (4617316753 / 250000000000) (9234634007 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (4617316753 / 250000000000) (9234634007 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-9234634007 / 500000000000) (-4617316753 / 250000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (337338955993 / 500000000000) (168669478497 / 250000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (337338955993 / 500000000000) (168669478497 / 250000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (479 / 2500)
  have hx41 : Bounds (337338955993 / 500000000000) (168669478497 / 250000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674658506677 / 1000000000000) (168669478497 / 250000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1917 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1917 / 10000000)
  have hx45 : Bounds (10001917 / 10000000) (10001917 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1917 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1917 / 10000000)
  have hx46 : Bounds (10001917 / 10000000) (10001917 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1917 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (191681 / 1000000000) (95841 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5796.1) (by simpa only [div_one] using reflection_log_5796.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (38343549 / 200000000000) (95859373 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1917 / 10000000)
  have hx49 : Bounds (-1917 / 10000000) (-1917 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1917 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998083 / 10000000) (9998083 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1917 / 10000000)
  have hx51 : Bounds (9998083 / 10000000) (9998083 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1917 / 10000000)
  have hx52 : Bounds (-1917 / 10000000) (-1917 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1917 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998083 / 10000000) (9998083 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1917 / 10000000)
  have hx54 : Bounds (9998083 / 10000000) (9998083 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-191719 / 1000000000) (-95859 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_5797.1) (by simpa only [div_one] using reflection_log_5797.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-23960281 / 125000000000) (-191681247 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (35497 / 1000000000000) (37499 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (4437 / 250000000000) (3 / 160000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (4437 / 250000000000) (3 / 160000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-3 / 160000000) (-4437 / 250000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (554517729 / 800000000) (173286790813 / 250000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (554517729 / 800000000) (173286790813 / 250000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1917 / 10000000)
  have hx64 : Bounds (554517729 / 800000000) (173286790813 / 250000000000) x64 := by
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
  have hx86 : Bounds (554517729 / 800000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1367805667927 / 1000000000000) (341956273747 / 250000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (683902833963 / 1000000000000) (341956273747 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (683902833963 / 1000000000000) (341956273747 / 500000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (10422545633813 / 1000000000000) (10448862223393 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7128008496073 / 1000000000000) (1429221596323 / 200000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7128008496073 / 1000000000000) (1429221596323 / 200000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(19269 / 200000)
  have hx95 : Bounds (219269 / 200000) (219269 / 200000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19269 / 200000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(19269 / 200000)
  have hx96 : Bounds (219269 / 200000) (219269 / 200000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19269 / 200000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (574887 / 6250000) (91981921 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_5798.1) (by simpa only [div_one] using reflection_log_5798.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (50421959041 / 500000000000) (100843919179 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(19269 / 200000)
  have hx99 : Bounds (-19269 / 200000) (-19269 / 200000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19269 / 200000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (180731 / 200000) (180731 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(19269 / 200000)
  have hx101 : Bounds (180731 / 200000) (180731 / 200000) x101 := by
    exact hx100
  let x102 : ℝ := -(19269 / 200000)
  have hx102 : Bounds (-19269 / 200000) (-19269 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19269 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (180731 / 200000) (180731 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(19269 / 200000)
  have hx104 : Bounds (180731 / 200000) (180731 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-101307629 / 1000000000) (-25326907 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_5799.1) (by simpa only [div_one] using reflection_log_5799.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-22886786371 / 250000000000) (-4577357229 / 50000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (4648386299 / 500000000000) (9296774599 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4648386299 / 1000000000000) (46483873 / 10000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4648386299 / 1000000000000) (46483873 / 10000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-46483873 / 10000000000) (-4648386299 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (6884987927 / 10000000000) (688498794701 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (6884987927 / 10000000000) (688498794701 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (19269 / 200000)
  have hx114 : Bounds (6884987927 / 10000000000) (688498794701 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(24147 / 250000)
  have hx116 : Bounds (274147 / 250000) (274147 / 250000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24147 / 250000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(24147 / 250000)
  have hx117 : Bounds (274147 / 250000) (274147 / 250000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24147 / 250000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (92203541 / 1000000000) (46101771 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_5800.1) (by simpa only [div_one] using reflection_log_5800.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (50554648309 / 500000000000) (20221859543 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(24147 / 250000)
  have hx120 : Bounds (-24147 / 250000) (-24147 / 250000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24147 / 250000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (225853 / 250000) (225853 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(24147 / 250000)
  have hx122 : Bounds (225853 / 250000) (225853 / 250000) x122 := by
    exact hx121
  let x123 : ℝ := -(24147 / 250000)
  have hx123 : Bounds (-24147 / 250000) (-24147 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24147 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (225853 / 250000) (225853 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(24147 / 250000)
  have hx125 : Bounds (225853 / 250000) (225853 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-101576573 / 1000000000) (-25394143 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_5801.1) (by simpa only [div_one] using reflection_log_5801.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-11470686871 / 125000000000) (-91765494063 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (186876033 / 20000000000) (2335950913 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (186876033 / 40000000000) (2335950913 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (186876033 / 40000000000) (2335950913 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2335950913 / 500000000000) (-186876033 / 40000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (344237639087 / 500000000000) (27539011207 / 40000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (344237639087 / 500000000000) (27539011207 / 40000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (24147 / 250000)
  have hx135 : Bounds (344237639087 / 500000000000) (27539011207 / 40000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(19269 / 200000)
  have hx136 : Bounds (343373989277 / 500000000000) (688491773489 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((19269 / 200000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(24147 / 250000)
  have hx137 : Bounds (344240042309 / 500000000000) (690228277729 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((24147 / 250000) : ℝ)) <;> norm_num
  have hc : Bounds (19269 / 200000) (24147 / 250000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(19269 / 200000) ≤ (688491773489 / 1000000000000) := hx136.2
      have h2 : (6884987927 / 10000000000) ≤ biasE (19269 / 200000) := hx114.1
      linarith
    · have h1 : biasE (24147 / 250000) ≤ (27539011207 / 40000000000) := hx135.2
      have h2 : (344240042309 / 500000000000) ≤ x93*(24147 / 250000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(24147 / 250000)
  have hx139 : Bounds (274147 / 250000) (274147 / 250000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24147 / 250000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(24147 / 250000)
  have hx140 : Bounds (274147 / 250000) (274147 / 250000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24147 / 250000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (92203541 / 1000000000) (46101771 / 500000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_5800.1) (by simpa only [div_one] using reflection_log_5800.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (50554648309 / 500000000000) (20221859543 / 200000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(24147 / 250000)
  have hx143 : Bounds (-24147 / 250000) (-24147 / 250000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24147 / 250000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (225853 / 250000) (225853 / 250000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(24147 / 250000)
  have hx145 : Bounds (225853 / 250000) (225853 / 250000) x145 := by
    exact hx144
  let x146 : ℝ := -(24147 / 250000)
  have hx146 : Bounds (-24147 / 250000) (-24147 / 250000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24147 / 250000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (225853 / 250000) (225853 / 250000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(24147 / 250000)
  have hx148 : Bounds (225853 / 250000) (225853 / 250000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-101576573 / 1000000000) (-25394143 / 250000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_5801.1) (by simpa only [div_one] using reflection_log_5801.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-11470686871 / 125000000000) (-91765494063 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (186876033 / 20000000000) (2335950913 / 250000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (186876033 / 40000000000) (2335950913 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (186876033 / 40000000000) (2335950913 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-2335950913 / 500000000000) (-186876033 / 40000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (344237639087 / 500000000000) (27539011207 / 40000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (344237639087 / 500000000000) (27539011207 / 40000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (24147 / 250000)
  have hx158 : Bounds (344237639087 / 500000000000) (27539011207 / 40000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(19269 / 200000)
  have hx160 : Bounds (219269 / 200000) (219269 / 200000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19269 / 200000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(19269 / 200000)
  have hx161 : Bounds (219269 / 200000) (219269 / 200000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19269 / 200000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (574887 / 6250000) (91981921 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_5798.1) (by simpa only [div_one] using reflection_log_5798.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (50421959041 / 500000000000) (100843919179 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(19269 / 200000)
  have hx164 : Bounds (-19269 / 200000) (-19269 / 200000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19269 / 200000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (180731 / 200000) (180731 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(19269 / 200000)
  have hx166 : Bounds (180731 / 200000) (180731 / 200000) x166 := by
    exact hx165
  let x167 : ℝ := -(19269 / 200000)
  have hx167 : Bounds (-19269 / 200000) (-19269 / 200000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19269 / 200000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (180731 / 200000) (180731 / 200000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(19269 / 200000)
  have hx169 : Bounds (180731 / 200000) (180731 / 200000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-101307629 / 1000000000) (-25326907 / 250000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_5799.1) (by simpa only [div_one] using reflection_log_5799.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-22886786371 / 250000000000) (-4577357229 / 50000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (4648386299 / 500000000000) (9296774599 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4648386299 / 1000000000000) (46483873 / 10000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4648386299 / 1000000000000) (46483873 / 10000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-46483873 / 10000000000) (-4648386299 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (6884987927 / 10000000000) (688498794701 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (6884987927 / 10000000000) (688498794701 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (19269 / 200000)
  have hx179 : Bounds (6884987927 / 10000000000) (688498794701 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (344237639087 / 500000000000) (688498794701 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-583077609 / 62500000000) (-371294361 / 40000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-1171629 / 125000000) (-2331427 / 250000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_5802.1) (by simpa only [div_one] using reflection_log_5803.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-1171629 / 250000000) (-2331427 / 500000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-1171629 / 250000000) (-2331427 / 500000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (2331427 / 500000000) (1171629 / 250000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (348905017 / 500000000) (697833697 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (348905017 / 500000000) (697833697 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (19269 / 200000) (24147 / 250000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-583077609 / 62500000000) (-371294361 / 40000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (219269 / 200000) (274147 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-24147 / 250000) (-19269 / 200000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (225853 / 250000) (180731 / 200000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (225853 / 250000) (180731 / 200000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1106617016449 / 1000000000000) (110691467459 / 100000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (606617016449 / 500000000000) (60691467459 / 50000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (606617016449 / 500000000000) (60691467459 / 50000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (48322387 / 250000000) (96890057 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_5804.1) (by simpa only [div_one] using reflection_log_5805.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (48322387 / 500000000) (96890057 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (48322387 / 500000000) (96890057 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (2979 / 2500) (11917 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1917 / 10000) (-479 / 2500) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8083 / 10000) (2021 / 2500) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8083 / 10000) (2021 / 2500) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (154626422563 / 125000000000) (77322776197 / 62500000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (92126422563 / 62500000000) (46072776197 / 31250000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (92126422563 / 62500000000) (46072776197 / 31250000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (77599047 / 200000000) (194101431 / 500000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_5806.1) (by simpa only [div_one] using reflection_log_5807.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (77599047 / 400000000) (194101431 / 1000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (77599047 / 400000000) (194101431 / 1000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (348905017 / 250000000) (697833697 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (19269 / 200000) (24147 / 250000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-583077609 / 62500000000) (-371294361 / 40000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (86643176641 / 62500000000) (55455401399 / 40000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (86643176641 / 62500000000) (55455401399 / 40000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (238606740559 / 250000000000) (238631106393 / 250000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (683902833963 / 500000000000) (341956273747 / 250000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (981428551263 / 1000000000000) (49076072207 / 50000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (981428551263 / 1000000000000) (49076072207 / 50000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1342403535081 / 1000000000000) (335637415641 / 250000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (348905017 / 500000000) (697833697 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (486938843551 / 1000000000000) (486971868669 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169895405487 / 500000000000) (339825379449 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169895405487 / 500000000000) (339825379449 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456136385839 / 1000000000000) (45623244851 / 100000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2191865140819 / 1000000000000) (548081687323 / 250000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (1045987593991 / 500000000000) (418525886207 / 200000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (1045987593991 / 500000000000) (418525886207 / 200000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-96890057 / 1000000000) (-48322387 / 500000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (348905017 / 250000000) (697833697 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (19269 / 200000) (24147 / 250000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-583077609 / 62500000000) (-371294361 / 40000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (86643176641 / 62500000000) (55455401399 / 40000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (86643176641 / 62500000000) (55455401399 / 40000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-134326925063 / 1000000000000) (-133977763601 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (201873865699 / 200000000000) (1009417096111 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (97247687953 / 1000000000000) (1218719731 / 12500000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (97247687953 / 1000000000000) (1218719731 / 12500000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (97247687953 / 500000000000) (1218719731 / 6250000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (19269 / 100000) (24147 / 125000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-24147 / 125000) (-19269 / 100000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (659687953 / 500000000000) (14407231 / 6250000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (659687953 / 500000000000) (14407231 / 6250000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (908357693 / 1000000000000) (1587097789 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-13341856737 / 100000000000) (-33097666453 / 250000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (683902833963 / 500000000000) (341956273747 / 250000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (981428551263 / 1000000000000) (49076072207 / 50000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (981428551263 / 1000000000000) (49076072207 / 50000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1342403535081 / 1000000000000) (335637415641 / 250000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (348905017 / 500000000) (697833697 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (486938843551 / 1000000000000) (486971868669 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169895405487 / 500000000000) (339825379449 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169895405487 / 500000000000) (339825379449 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456136385839 / 1000000000000) (45623244851 / 100000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2191865140819 / 1000000000000) (548081687323 / 250000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-146248547049 / 500000000000) (-290182485363 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-146248547049 / 500000000000) (-290182485363 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (19269 / 50000) (24147 / 62500) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (201873865699 / 200000000000) (1009417096111 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (77798150363 / 200000000000) (389990313917 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (77798150363 / 200000000000) (389990313917 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (57807 / 200000) (72441 / 250000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691299995501 / 1000000000000) (138271230817 / 200000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (723216242519 / 500000000000) (361637496929 / 250000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (1633084427 / 3906250000) (419158110641 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (1633084427 / 3906250000) (419158110641 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-419158110641 / 1000000000000) (-1633084427 / 3906250000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-15083679413 / 500000000000) (-5615859879 / 200000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-15083679413 / 500000000000) (-5615859879 / 200000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-7891137867 / 125000000000) (-5874119763 / 100000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-177813098517 / 500000000000) (-348923682993 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (348905017 / 250000000) (697833697 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (19269 / 200000) (24147 / 250000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (371294361 / 40000000000) (583077609 / 62500000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-583077609 / 62500000000) (-371294361 / 40000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (86643176641 / 62500000000) (55455401399 / 40000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (86643176641 / 62500000000) (55455401399 / 40000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (26712437931 / 200000000000) (133908157759 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (61916922391 / 62500000000) (39628705639 / 40000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (981428551263 / 1000000000000) (49076072207 / 50000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (981428551263 / 1000000000000) (49076072207 / 50000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (348905017 / 500000000) (697833697 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (486938843551 / 1000000000000) (486971868669 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (486938843551 / 1000000000000) (486971868669 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (477895683779 / 1000000000000) (29873333237 / 62500000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2092166933771 / 1000000000000) (523126716741 / 250000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (139717198399 / 500000000000) (140101869827 / 500000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (139717198399 / 500000000000) (140101869827 / 500000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (9345350229 / 500000000000) (9373934509 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (88395747329 / 125000000000) (707246663719 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (88395747329 / 125000000000) (707246663719 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (250041860667 / 500000000000) (250098921671 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (250041860667 / 500000000000) (250098921671 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-177883456793 / 1000000000000) (-43622763463 / 250000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (1045987593991 / 250000000000) (418525886207 / 100000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (9345350229 / 500000000000) (9373934509 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (88395747329 / 125000000000) (707246663719 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1479373681083 / 500000000000) (2960010367 / 1000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-96890057 / 1000000000) (-48322387 / 500000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (194215121 / 2000000000) (97456657 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (194215121 / 2000000000) (97456657 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (11492669539 / 40000000000) (144236357527 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (54716640841 / 500000000000) (56990830601 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (479 / 2500) (1917 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (229441 / 6250000) (3674889 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (229441 / 6250000) (3674889 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3674889 / 100000000) (-229441 / 6250000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96325111 / 100000000) (6020559 / 6250000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96325111 / 100000000) (6020559 / 6250000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (64881849011 / 62500000000) (103815089297 / 100000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (64881849011 / 62500000000) (103815089297 / 100000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (64881849011 / 62500000000) (103815089297 / 100000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (36260440683 / 125000000000) (36361720317 / 125000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (199758403573 / 500000000000) (202437711869 / 500000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (344237639087 / 500000000000) (688498794701 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (29624888041 / 62500000000) (94806118061 / 200000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (29624888041 / 62500000000) (94806118061 / 200000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (37874050183 / 200000000000) (38384667223 / 200000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (23861712991 / 50000000000) (477257221443 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2095306168393 / 1000000000000) (26192587273 / 12500000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (99197163713 / 250000000000) (201078749237 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (99197163713 / 250000000000) (201078749237 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (14772902699052578175646997 / 36247130672481000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_416 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((479 / 2500):ℝ) ((1917 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (14772902699052578175646997 / 36247130672481000000000000) := by
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
  have hsl : (478521 / 5000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1918917 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1917 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_416 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_416 {a z : ℝ}
    (ha : a ∈ Set.Icc ((479 / 2500):ℝ) ((1917 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_416 ha ⟨hz.1.le,hz.2⟩ hs) (M := (14772902699052578175646997 / 36247130672481000000000000))
  exact lt_of_lt_of_le (by norm_num : (14772902699052578175646997 / 36247130672481000000000000) < 2*((479 / 2500):ℝ)/(1-((479 / 2500):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0417 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_417 (a z s c : ℝ)
    (ha : Bounds (1917 / 10000) (959 / 5000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1915083 / 20000000) (959959 / 10000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (7567529821006022997627331669 / 18557054018324642000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(959 / 5000)
  have hx1 : Bounds (5959 / 5000) (5959 / 5000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((959 / 5000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(959 / 5000)
  have hx2 : Bounds (5959 / 5000) (5959 / 5000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((959 / 5000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (175464769 / 1000000000) (17546477 / 100000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_5808.1) (by simpa only [div_one] using reflection_log_5808.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (104559455847 / 500000000000) (104559456443 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(959 / 5000)
  have hx5 : Bounds (-959 / 5000) (-959 / 5000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((959 / 5000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (4041 / 5000) (4041 / 5000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(959 / 5000)
  have hx7 : Bounds (4041 / 5000) (4041 / 5000) x7 := by
    exact hx6
  let x8 : ℝ := -(959 / 5000)
  have hx8 : Bounds (-959 / 5000) (-959 / 5000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((959 / 5000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (4041 / 5000) (4041 / 5000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(959 / 5000)
  have hx10 : Bounds (4041 / 5000) (4041 / 5000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-212945727 / 1000000000) (-106472863 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_5809.1) (by simpa only [div_one] using reflection_log_5809.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-86051368281 / 500000000000) (-172102735753 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (9254043783 / 250000000000) (37016177133 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (9254043783 / 500000000000) (18508088567 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (9254043783 / 500000000000) (18508088567 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18508088567 / 1000000000000) (-9254043783 / 500000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674639091433 / 1000000000000) (337319546717 / 500000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674639091433 / 1000000000000) (337319546717 / 500000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (959 / 5000)
  have hx20 : Bounds (674639091433 / 1000000000000) (337319546717 / 500000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1917 / 10000)
  have hx22 : Bounds (11917 / 10000) (11917 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1917 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1917 / 10000)
  have hx23 : Bounds (11917 / 10000) (11917 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1917 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (175380859 / 1000000000) (8769043 / 50000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_5794.1) (by simpa only [div_one] using reflection_log_5794.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (20900136967 / 100000000000) (104500685431 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1917 / 10000)
  have hx26 : Bounds (-1917 / 10000) (-1917 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1917 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8083 / 10000) (8083 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1917 / 10000)
  have hx28 : Bounds (8083 / 10000) (8083 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1917 / 10000)
  have hx29 : Bounds (-1917 / 10000) (-1917 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1917 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8083 / 10000) (8083 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1917 / 10000)
  have hx31 : Bounds (8083 / 10000) (8083 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-212822003 / 1000000000) (-106411001 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_5795.1) (by simpa only [div_one] using reflection_log_5795.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-6880961001 / 40000000000) (-21503003027 / 125000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (7395468929 / 200000000000) (18488673323 / 500000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (9244336161 / 500000000000) (18488673323 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (9244336161 / 500000000000) (18488673323 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18488673323 / 1000000000000) (-9244336161 / 500000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (674658506677 / 1000000000000) (337329254339 / 500000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (674658506677 / 1000000000000) (337329254339 / 500000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1917 / 10000)
  have hx41 : Bounds (674658506677 / 1000000000000) (337329254339 / 500000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674639091433 / 1000000000000) (337329254339 / 500000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (959 / 5000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(959 / 5000000)
  have hx45 : Bounds (5000959 / 5000000) (5000959 / 5000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((959 / 5000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(959 / 5000000)
  have hx46 : Bounds (5000959 / 5000000) (5000959 / 5000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((959 / 5000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (191781 / 1000000000) (95891 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5810.1) (by simpa only [div_one] using reflection_log_5810.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (191817783 / 1000000000000) (5994337 / 31250000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(959 / 5000000)
  have hx49 : Bounds (-959 / 5000000) (-959 / 5000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((959 / 5000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (4999041 / 5000000) (4999041 / 5000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(959 / 5000000)
  have hx51 : Bounds (4999041 / 5000000) (4999041 / 5000000) x51 := by
    exact hx50
  let x52 : ℝ := -(959 / 5000000)
  have hx52 : Bounds (-959 / 5000000) (-959 / 5000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((959 / 5000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (4999041 / 5000000) (4999041 / 5000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(959 / 5000000)
  have hx54 : Bounds (4999041 / 5000000) (4999041 / 5000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-191819 / 1000000000) (-95909 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_5811.1) (by simpa only [div_one] using reflection_log_5811.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-19178221 / 100000000000) (-191781209 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (35573 / 1000000000000) (1503 / 40000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (8893 / 500000000000) (4697 / 250000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (8893 / 500000000000) (4697 / 250000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-4697 / 250000000000) (-8893 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (173286790303 / 250000000000) (346573581607 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (173286790303 / 250000000000) (346573581607 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (959 / 5000000)
  have hx64 : Bounds (173286790303 / 250000000000) (346573581607 / 500000000000) x64 := by
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
  have hx86 : Bounds (173286790303 / 250000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (273557250529 / 200000000000) (683902844839 / 500000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (341946563161 / 500000000000) (683902844839 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (341946563161 / 500000000000) (683902844839 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (10417111564139 / 1000000000000) (10443411591039 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (1781047748711 / 250000000000) (7142278896937 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (1781047748711 / 250000000000) (7142278896937 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(24099 / 250000)
  have hx95 : Bounds (274099 / 250000) (274099 / 250000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24099 / 250000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(24099 / 250000)
  have hx96 : Bounds (274099 / 250000) (274099 / 250000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24099 / 250000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (92028437 / 1000000000) (46014219 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_5812.1) (by simpa only [div_one] using reflection_log_5812.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (100899610213 / 1000000000000) (10089961131 / 100000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(24099 / 250000)
  have hx99 : Bounds (-24099 / 250000) (-24099 / 250000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24099 / 250000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (225901 / 250000) (225901 / 250000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(24099 / 250000)
  have hx101 : Bounds (225901 / 250000) (225901 / 250000) x101 := by
    exact hx100
  let x102 : ℝ := -(24099 / 250000)
  have hx102 : Bounds (-24099 / 250000) (-24099 / 250000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24099 / 250000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (225901 / 250000) (225901 / 250000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(24099 / 250000)
  have hx104 : Bounds (225901 / 250000) (225901 / 250000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-25341017 / 250000000) (-101364067 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_5813.1) (by simpa only [div_one] using reflection_log_5813.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-45796488651 / 500000000000) (-91592976397 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (9306632911 / 1000000000000) (9306634913 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (930663291 / 200000000000) (4653317457 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (930663291 / 200000000000) (4653317457 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4653317457 / 1000000000000) (-930663291 / 200000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688493862543 / 1000000000000) (137698772909 / 200000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688493862543 / 1000000000000) (137698772909 / 200000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (24099 / 250000)
  have hx114 : Bounds (688493862543 / 1000000000000) (137698772909 / 200000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(96639 / 1000000)
  have hx116 : Bounds (1096639 / 1000000) (1096639 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96639 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(96639 / 1000000)
  have hx117 : Bounds (1096639 / 1000000) (1096639 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96639 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (92250047 / 1000000000) (1441407 / 15625000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_5814.1) (by simpa only [div_one] using reflection_log_5814.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (25291249823 / 250000000000) (101165000389 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(96639 / 1000000)
  have hx120 : Bounds (-96639 / 1000000) (-96639 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96639 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (903361 / 1000000) (903361 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(96639 / 1000000)
  have hx122 : Bounds (903361 / 1000000) (903361 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(96639 / 1000000)
  have hx123 : Bounds (-96639 / 1000000) (-96639 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96639 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (903361 / 1000000) (903361 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(96639 / 1000000)
  have hx125 : Bounds (903361 / 1000000) (903361 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-101633027 / 1000000000) (-50816513 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_5815.1) (by simpa only [div_one] using reflection_log_5815.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-11476414113 / 125000000000) (-5738207 / 62500000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (2338421597 / 250000000000) (9353688389 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2338421597 / 500000000000) (935368839 / 200000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2338421597 / 500000000000) (935368839 / 200000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-935368839 / 200000000000) (-2338421597 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (137694067161 / 200000000000) (344235168903 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (137694067161 / 200000000000) (344235168903 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (96639 / 1000000)
  have hx135 : Bounds (137694067161 / 200000000000) (344235168903 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(24099 / 250000)
  have hx136 : Bounds (343371757569 / 500000000000) (13769742331 / 20000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((24099 / 250000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(96639 / 1000000)
  have hx137 : Bounds (13769493871 / 20000000000) (345111345161 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((96639 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (24099 / 250000) (96639 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(24099 / 250000) ≤ (13769742331 / 20000000000) := hx136.2
      have h2 : (688493862543 / 1000000000000) ≤ biasE (24099 / 250000) := hx114.1
      linarith
    · have h1 : biasE (96639 / 1000000) ≤ (344235168903 / 500000000000) := hx135.2
      have h2 : (13769493871 / 20000000000) ≤ x93*(96639 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(96639 / 1000000)
  have hx139 : Bounds (1096639 / 1000000) (1096639 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96639 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(96639 / 1000000)
  have hx140 : Bounds (1096639 / 1000000) (1096639 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96639 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (92250047 / 1000000000) (1441407 / 15625000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_5814.1) (by simpa only [div_one] using reflection_log_5814.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (25291249823 / 250000000000) (101165000389 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(96639 / 1000000)
  have hx143 : Bounds (-96639 / 1000000) (-96639 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96639 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (903361 / 1000000) (903361 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(96639 / 1000000)
  have hx145 : Bounds (903361 / 1000000) (903361 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(96639 / 1000000)
  have hx146 : Bounds (-96639 / 1000000) (-96639 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96639 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (903361 / 1000000) (903361 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(96639 / 1000000)
  have hx148 : Bounds (903361 / 1000000) (903361 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-101633027 / 1000000000) (-50816513 / 500000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_5815.1) (by simpa only [div_one] using reflection_log_5815.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-11476414113 / 125000000000) (-5738207 / 62500000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (2338421597 / 250000000000) (9353688389 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (2338421597 / 500000000000) (935368839 / 200000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (2338421597 / 500000000000) (935368839 / 200000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-935368839 / 200000000000) (-2338421597 / 500000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (137694067161 / 200000000000) (344235168903 / 500000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (137694067161 / 200000000000) (344235168903 / 500000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (96639 / 1000000)
  have hx158 : Bounds (137694067161 / 200000000000) (344235168903 / 500000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(24099 / 250000)
  have hx160 : Bounds (274099 / 250000) (274099 / 250000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24099 / 250000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(24099 / 250000)
  have hx161 : Bounds (274099 / 250000) (274099 / 250000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24099 / 250000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (92028437 / 1000000000) (46014219 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_5812.1) (by simpa only [div_one] using reflection_log_5812.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (100899610213 / 1000000000000) (10089961131 / 100000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(24099 / 250000)
  have hx164 : Bounds (-24099 / 250000) (-24099 / 250000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24099 / 250000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (225901 / 250000) (225901 / 250000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(24099 / 250000)
  have hx166 : Bounds (225901 / 250000) (225901 / 250000) x166 := by
    exact hx165
  let x167 : ℝ := -(24099 / 250000)
  have hx167 : Bounds (-24099 / 250000) (-24099 / 250000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24099 / 250000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (225901 / 250000) (225901 / 250000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(24099 / 250000)
  have hx169 : Bounds (225901 / 250000) (225901 / 250000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-25341017 / 250000000) (-101364067 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_5813.1) (by simpa only [div_one] using reflection_log_5813.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-45796488651 / 500000000000) (-91592976397 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (9306632911 / 1000000000000) (9306634913 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (930663291 / 200000000000) (4653317457 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (930663291 / 200000000000) (4653317457 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4653317457 / 1000000000000) (-930663291 / 200000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688493862543 / 1000000000000) (137698772909 / 200000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688493862543 / 1000000000000) (137698772909 / 200000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (24099 / 250000)
  have hx179 : Bounds (688493862543 / 1000000000000) (137698772909 / 200000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (137694067161 / 200000000000) (137698772909 / 200000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-9339096321 / 1000000000000) (-580761801 / 62500000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-469149 / 50000000) (-933563 / 100000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_5816.1) (by simpa only [div_one] using reflection_log_5817.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-469149 / 100000000) (-933563 / 200000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-469149 / 100000000) (-933563 / 200000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (933563 / 200000000) (469149 / 100000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (139562999 / 200000000) (697838671 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (139562999 / 200000000) (697838671 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (24099 / 250000) (96639 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-9339096321 / 1000000000000) (-580761801 / 62500000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (274099 / 250000) (1096639 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-96639 / 1000000) (-24099 / 250000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (903361 / 1000000) (225901 / 250000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (903361 / 1000000) (225901 / 250000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1106679474637 / 1000000000000) (553488583191 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (606679474637 / 500000000000) (303488583191 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (606679474637 / 500000000000) (303488583191 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (24174063 / 125000000) (7755323 / 40000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_5818.1) (by simpa only [div_one] using reflection_log_5819.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (24174063 / 250000000) (7755323 / 80000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (24174063 / 250000000) (7755323 / 80000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11917 / 10000) (5959 / 5000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-959 / 5000) (-1917 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (4041 / 5000) (8083 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (4041 / 5000) (8083 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1237164419151 / 1000000000000) (123731749567 / 100000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (737164419151 / 500000000000) (73731749567 / 50000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (737164419151 / 500000000000) (73731749567 / 50000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (388202861 / 1000000000) (3034457 / 7812500) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_5820.1) (by simpa only [div_one] using reflection_log_5821.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (388202861 / 2000000000) (3034457 / 15625000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (388202861 / 2000000000) (3034457 / 15625000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (139562999 / 100000000) (697838671 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (24099 / 250000) (96639 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-9339096321 / 1000000000000) (-580761801 / 62500000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386290893679 / 1000000000000) (43324536037 / 31250000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386290893679 / 1000000000000) (43324536037 / 31250000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477210078547 / 500000000000) (119314708983 / 125000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (341946563161 / 250000000000) (683902844839 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (490704513039 / 500000000000) (981501967141 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (490704513039 / 500000000000) (981501967141 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (134235777409 / 100000000000) (671251987543 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (139562999 / 200000000) (697838671 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (243472883623 / 500000000000) (60872351343 / 125000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (42474757267 / 125000000000) (67966529219 / 200000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (42474757267 / 125000000000) (67966529219 / 200000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456130564959 / 1000000000000) (456226678247 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (136993303943 / 62500000000) (87694189061 / 40000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2091986730721 / 1000000000000) (2092641329463 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2091986730721 / 1000000000000) (2092641329463 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-7755323 / 80000000) (-24174063 / 250000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (139562999 / 100000000) (697838671 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (24099 / 250000) (96639 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-9339096321 / 1000000000000) (-580761801 / 62500000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386290893679 / 1000000000000) (43324536037 / 31250000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386290893679 / 1000000000000) (43324536037 / 31250000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-134398308317 / 1000000000000) (-167561417 / 1250000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (504689671723 / 500000000000) (63089196079 / 62500000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (9730013119 / 100000000000) (97550029119 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (9730013119 / 100000000000) (97550029119 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (9730013119 / 50000000000) (97550029119 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (24099 / 125000) (96639 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-96639 / 500000) (-24099 / 125000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (66113119 / 50000000000) (1154029119 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (66113119 / 50000000000) (1154029119 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (113792303 / 125000000000) (49658873 / 31250000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-133487969893 / 1000000000000) (-517422069 / 3906250000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (341946563161 / 250000000000) (683902844839 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (490704513039 / 500000000000) (981501967141 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (490704513039 / 500000000000) (981501967141 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (134235777409 / 100000000000) (671251987543 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (139562999 / 200000000) (697838671 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (243472883623 / 500000000000) (60872351343 / 125000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (42474757267 / 125000000000) (67966529219 / 200000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (42474757267 / 125000000000) (67966529219 / 200000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456130564959 / 1000000000000) (456226678247 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (136993303943 / 62500000000) (87694189061 / 40000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-29265298173 / 100000000000) (-145169118751 / 500000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-29265298173 / 100000000000) (-145169118751 / 500000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (24099 / 62500) (96639 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (504689671723 / 500000000000) (63089196079 / 62500000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (389200524763 / 1000000000000) (390200116473 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (389200524763 / 1000000000000) (390200116473 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (72297 / 250000) (289917 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691298033547 / 1000000000000) (345677111153 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (723218263327 / 500000000000) (144655409313 / 100000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (41829208627 / 100000000000) (209690311509 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (41829208627 / 100000000000) (209690311509 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-209690311509 / 500000000000) (-41829208627 / 100000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-6036019651 / 200000000000) (-28091969797 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-6036019651 / 200000000000) (-28091969797 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-7894515117 / 125000000000) (-11753605611 / 200000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-177904551333 / 500000000000) (-349106265557 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (139562999 / 100000000) (697838671 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (24099 / 250000) (96639 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (580761801 / 62500000000) (9339096321 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-9339096321 / 1000000000000) (-580761801 / 62500000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386290893679 / 1000000000000) (43324536037 / 31250000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386290893679 / 1000000000000) (43324536037 / 31250000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (133632896987 / 1000000000000) (133978874819 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (990660903679 / 1000000000000) (61919238199 / 62500000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (490704513039 / 500000000000) (981501967141 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (490704513039 / 500000000000) (981501967141 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (139562999 / 200000000) (697838671 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (243472883623 / 500000000000) (60872351343 / 125000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (243472883623 / 500000000000) (60872351343 / 125000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (95578594237 / 200000000000) (238985330351 / 500000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (65380582051 / 31250000000) (418503748871 / 200000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (279583890757 / 1000000000000) (280353306907 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (279583890757 / 1000000000000) (280353306907 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (9355300747 / 500000000000) (9383900481 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (707180937299 / 1000000000000) (707261665507 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (707180937299 / 1000000000000) (707261665507 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (500104878079 / 1000000000000) (62527382937 / 125000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (500104878079 / 1000000000000) (62527382937 / 125000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-177982496119 / 1000000000000) (-43647436593 / 250000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2091986730721 / 500000000000) (2092641329463 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (9355300747 / 500000000000) (9383900481 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (707180937299 / 1000000000000) (707261665507 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (184926642131 / 62500000000) (296008998397 / 100000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-7755323 / 80000000) (-24174063 / 250000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (97159893 / 1000000000) (24377249 / 250000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (97159893 / 1000000000) (24377249 / 250000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (71869811049 / 250000000000) (288635402407 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (109496748077 / 1000000000000) (22809131207 / 200000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1917 / 10000) (959 / 5000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3674889 / 100000000) (919681 / 25000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3674889 / 100000000) (919681 / 25000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-919681 / 25000000) (-3674889 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (24080319 / 25000000) (96325111 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (24080319 / 25000000) (96325111 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1038150892969 / 1000000000000) (1038192226607 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1038150892969 / 1000000000000) (1038192226607 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1038150892969 / 1000000000000) (1038192226607 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (290250265849 / 1000000000000) (58212124787 / 200000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (199873506963 / 500000000000) (40510627997 / 100000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (137694067161 / 200000000000) (137698772909 / 200000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (473991403283 / 1000000000000) (474023801517 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (473991403283 / 1000000000000) (474023801517 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (23684581011 / 125000000000) (3840600377 / 20000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (119307719631 / 250000000000) (29828365771 / 62500000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (419064191983 / 200000000000) (419084365661 / 200000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (397014392153 / 1000000000000) (402383893189 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (397014392153 / 1000000000000) (402383893189 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (7567529821006022997627331669 / 18557054018324642000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_417 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1917 / 10000):ℝ) ((959 / 5000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (7567529821006022997627331669 / 18557054018324642000000000000) := by
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
  have hsl : (1915083 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (959959 / 10000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (959 / 5000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_417 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_417 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1917 / 10000):ℝ) ((959 / 5000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_417 ha ⟨hz.1.le,hz.2⟩ hs) (M := (7567529821006022997627331669 / 18557054018324642000000000000))
  exact lt_of_lt_of_le (by norm_num : (7567529821006022997627331669 / 18557054018324642000000000000) < 2*((1917 / 10000):ℝ)/(1-((1917 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0418 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_418 (a z s c : ℝ)
    (ha : Bounds (959 / 5000) (1919 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (958041 / 10000000) (1920919 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (473208328343686861962106559 / 1159723526283522000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1919 / 10000)
  have hx1 : Bounds (11919 / 10000) (11919 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1919 / 10000)
  have hx2 : Bounds (11919 / 10000) (11919 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (685737 / 3906250) (175548673 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_5822.1) (by simpa only [div_one] using reflection_log_5822.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (52309115539 / 250000000000) (209236463349 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1919 / 10000)
  have hx5 : Bounds (-1919 / 10000) (-1919 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8081 / 10000) (8081 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1919 / 10000)
  have hx7 : Bounds (8081 / 10000) (8081 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1919 / 10000)
  have hx8 : Bounds (-1919 / 10000) (-1919 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8081 / 10000) (8081 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1919 / 10000)
  have hx10 : Bounds (8081 / 10000) (8081 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-106534733 / 500000000) (-42613893 / 200000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_5823.1) (by simpa only [div_one] using reflection_log_5823.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-6887257419 / 40000000000) (-86090717333 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (37055026681 / 1000000000000) (37055028683 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (926375667 / 50000000000) (9263757171 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (926375667 / 50000000000) (9263757171 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-9263757171 / 500000000000) (-926375667 / 50000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (337309832829 / 500000000000) (33730983383 / 50000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (337309832829 / 500000000000) (33730983383 / 50000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1919 / 10000)
  have hx20 : Bounds (337309832829 / 500000000000) (33730983383 / 50000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(959 / 5000)
  have hx22 : Bounds (5959 / 5000) (5959 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((959 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(959 / 5000)
  have hx23 : Bounds (5959 / 5000) (5959 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((959 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (175464769 / 1000000000) (17546477 / 100000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_5808.1) (by simpa only [div_one] using reflection_log_5808.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (104559455847 / 500000000000) (104559456443 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(959 / 5000)
  have hx26 : Bounds (-959 / 5000) (-959 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((959 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4041 / 5000) (4041 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(959 / 5000)
  have hx28 : Bounds (4041 / 5000) (4041 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(959 / 5000)
  have hx29 : Bounds (-959 / 5000) (-959 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((959 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4041 / 5000) (4041 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(959 / 5000)
  have hx31 : Bounds (4041 / 5000) (4041 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-212945727 / 1000000000) (-106472863 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_5809.1) (by simpa only [div_one] using reflection_log_5809.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-86051368281 / 500000000000) (-172102735753 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (9254043783 / 250000000000) (37016177133 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (9254043783 / 500000000000) (18508088567 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (9254043783 / 500000000000) (18508088567 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18508088567 / 1000000000000) (-9254043783 / 500000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (674639091433 / 1000000000000) (337319546717 / 500000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (674639091433 / 1000000000000) (337319546717 / 500000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (959 / 5000)
  have hx41 : Bounds (674639091433 / 1000000000000) (337319546717 / 500000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (337309832829 / 500000000000) (337319546717 / 500000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1919 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1919 / 10000000)
  have hx45 : Bounds (10001919 / 10000000) (10001919 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1919 / 10000000)
  have hx46 : Bounds (10001919 / 10000000) (10001919 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (191881 / 1000000000) (95941 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5824.1) (by simpa only [div_one] using reflection_log_5824.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (191917821 / 1000000000000) (191918823 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1919 / 10000000)
  have hx49 : Bounds (-1919 / 10000000) (-1919 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998081 / 10000000) (9998081 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1919 / 10000000)
  have hx51 : Bounds (9998081 / 10000000) (9998081 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1919 / 10000000)
  have hx52 : Bounds (-1919 / 10000000) (-1919 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998081 / 10000000) (9998081 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1919 / 10000000)
  have hx54 : Bounds (9998081 / 10000000) (9998081 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-191919 / 1000000000) (-95959 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_5825.1) (by simpa only [div_one] using reflection_log_5825.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-191882171 / 1000000000000) (-19188117 / 100000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (713 / 20000000000) (37653 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (713 / 40000000000) (18827 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (713 / 40000000000) (18827 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-18827 / 1000000000000) (-713 / 40000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147161173 / 1000000000000) (27725886527 / 40000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147161173 / 1000000000000) (27725886527 / 40000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1919 / 10000000)
  have hx64 : Bounds (693147161173 / 1000000000000) (27725886527 / 40000000000) x64 := by
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
  have hx86 : Bounds (693147161173 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1367766826831 / 1000000000000) (683893137217 / 500000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (136776682683 / 200000000000) (683893137217 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (136776682683 / 200000000000) (683893137217 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (2082336631581 / 200000000000) (10437966642347 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7120377417423 / 1000000000000) (3569226876601 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7120377417423 / 1000000000000) (3569226876601 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(96447 / 1000000)
  have hx95 : Bounds (1096447 / 1000000) (1096447 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96447 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(96447 / 1000000)
  have hx96 : Bounds (1096447 / 1000000) (1096447 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96447 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (11509369 / 125000000) (92074953 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_5826.1) (by simpa only [div_one] using reflection_log_5826.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (20191060979 / 200000000000) (12619413249 / 125000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(96447 / 1000000)
  have hx99 : Bounds (-96447 / 1000000) (-96447 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96447 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (903553 / 1000000) (903553 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(96447 / 1000000)
  have hx101 : Bounds (903553 / 1000000) (903553 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(96447 / 1000000)
  have hx102 : Bounds (-96447 / 1000000) (-96447 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96447 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (903553 / 1000000) (903553 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(96447 / 1000000)
  have hx104 : Bounds (903553 / 1000000) (903553 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-10142051 / 100000000) (-101420509 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_5827.1) (by simpa only [div_one] using reflection_log_5827.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-91638806073 / 1000000000000) (-5727425323 / 62500000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (4658249411 / 500000000000) (1164562603 / 125000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4658249411 / 1000000000000) (1164562603 / 250000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4658249411 / 1000000000000) (1164562603 / 250000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-1164562603 / 250000000000) (-4658249411 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (172122232397 / 250000000000) (688488931589 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (172122232397 / 250000000000) (688488931589 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (96447 / 1000000)
  have hx114 : Bounds (172122232397 / 250000000000) (688488931589 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(9669 / 100000)
  have hx116 : Bounds (109669 / 100000) (109669 / 100000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9669 / 100000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(9669 / 100000)
  have hx117 : Bounds (109669 / 100000) (109669 / 100000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9669 / 100000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (11537069 / 125000000) (92296553 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_5828.1) (by simpa only [div_one] using reflection_log_5828.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (25305176403 / 250000000000) (10122070671 / 100000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(9669 / 100000)
  have hx120 : Bounds (-9669 / 100000) (-9669 / 100000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9669 / 100000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (90331 / 100000) (90331 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(9669 / 100000)
  have hx122 : Bounds (90331 / 100000) (90331 / 100000) x122 := by
    exact hx121
  let x123 : ℝ := -(9669 / 100000)
  have hx123 : Bounds (-9669 / 100000) (-9669 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9669 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (90331 / 100000) (90331 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(9669 / 100000)
  have hx125 : Bounds (90331 / 100000) (90331 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-20337897 / 200000000) (-25422371 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_5829.1) (by simpa only [div_one] using reflection_log_5829.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-11482141087 / 125000000000) (-5741070487 / 62500000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (2340894229 / 250000000000) (4681789459 / 500000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2340894229 / 500000000000) (4681789459 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2340894229 / 500000000000) (4681789459 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4681789459 / 1000000000000) (-2340894229 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (688465390541 / 1000000000000) (344232696271 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (688465390541 / 1000000000000) (344232696271 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (9669 / 100000)
  have hx135 : Bounds (688465390541 / 1000000000000) (344232696271 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(96447 / 1000000)
  have hx136 : Bounds (343369520389 / 500000000000) (43030153071 / 62500000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((96447 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(9669 / 100000)
  have hx137 : Bounds (68846929249 / 100000000000) (345108546699 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((9669 / 100000) : ℝ)) <;> norm_num
  have hc : Bounds (96447 / 1000000) (9669 / 100000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(96447 / 1000000) ≤ (43030153071 / 62500000000) := hx136.2
      have h2 : (172122232397 / 250000000000) ≤ biasE (96447 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (9669 / 100000) ≤ (344232696271 / 500000000000) := hx135.2
      have h2 : (68846929249 / 100000000000) ≤ x93*(9669 / 100000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(9669 / 100000)
  have hx139 : Bounds (109669 / 100000) (109669 / 100000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9669 / 100000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(9669 / 100000)
  have hx140 : Bounds (109669 / 100000) (109669 / 100000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9669 / 100000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (11537069 / 125000000) (92296553 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_5828.1) (by simpa only [div_one] using reflection_log_5828.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (25305176403 / 250000000000) (10122070671 / 100000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(9669 / 100000)
  have hx143 : Bounds (-9669 / 100000) (-9669 / 100000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9669 / 100000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (90331 / 100000) (90331 / 100000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(9669 / 100000)
  have hx145 : Bounds (90331 / 100000) (90331 / 100000) x145 := by
    exact hx144
  let x146 : ℝ := -(9669 / 100000)
  have hx146 : Bounds (-9669 / 100000) (-9669 / 100000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9669 / 100000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (90331 / 100000) (90331 / 100000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(9669 / 100000)
  have hx148 : Bounds (90331 / 100000) (90331 / 100000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-20337897 / 200000000) (-25422371 / 250000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_5829.1) (by simpa only [div_one] using reflection_log_5829.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-11482141087 / 125000000000) (-5741070487 / 62500000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (2340894229 / 250000000000) (4681789459 / 500000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (2340894229 / 500000000000) (4681789459 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (2340894229 / 500000000000) (4681789459 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4681789459 / 1000000000000) (-2340894229 / 500000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (688465390541 / 1000000000000) (344232696271 / 500000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (688465390541 / 1000000000000) (344232696271 / 500000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (9669 / 100000)
  have hx158 : Bounds (688465390541 / 1000000000000) (344232696271 / 500000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(96447 / 1000000)
  have hx160 : Bounds (1096447 / 1000000) (1096447 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96447 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(96447 / 1000000)
  have hx161 : Bounds (1096447 / 1000000) (1096447 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96447 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (11509369 / 125000000) (92074953 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_5826.1) (by simpa only [div_one] using reflection_log_5826.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (20191060979 / 200000000000) (12619413249 / 125000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(96447 / 1000000)
  have hx164 : Bounds (-96447 / 1000000) (-96447 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96447 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (903553 / 1000000) (903553 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(96447 / 1000000)
  have hx166 : Bounds (903553 / 1000000) (903553 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(96447 / 1000000)
  have hx167 : Bounds (-96447 / 1000000) (-96447 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96447 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (903553 / 1000000) (903553 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(96447 / 1000000)
  have hx169 : Bounds (903553 / 1000000) (903553 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-10142051 / 100000000) (-101420509 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_5827.1) (by simpa only [div_one] using reflection_log_5827.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-91638806073 / 1000000000000) (-5727425323 / 62500000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (4658249411 / 500000000000) (1164562603 / 125000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4658249411 / 1000000000000) (1164562603 / 250000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4658249411 / 1000000000000) (1164562603 / 250000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-1164562603 / 250000000000) (-4658249411 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (172122232397 / 250000000000) (688488931589 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (172122232397 / 250000000000) (688488931589 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (96447 / 1000000)
  have hx179 : Bounds (172122232397 / 250000000000) (688488931589 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (688465390541 / 1000000000000) (688488931589 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-93489561 / 10000000000) (-9302023809 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-2348233 / 250000000) (-9345557 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_5830.1) (by simpa only [div_one] using reflection_log_5831.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-2348233 / 500000000) (-9345557 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-2348233 / 500000000) (-9345557 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (9345557 / 2000000000) (2348233 / 500000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1395639917 / 2000000000) (697843647 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1395639917 / 2000000000) (697843647 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (96447 / 1000000) (9669 / 100000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-93489561 / 10000000000) (-9302023809 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1096447 / 1000000) (109669 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-9669 / 100000) (-96447 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (90331 / 100000) (903553 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (90331 / 100000) (903553 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (8853935519 / 8000000000) (69189979077 / 62500000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (4853935519 / 4000000000) (37939979077 / 31250000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (4853935519 / 4000000000) (37939979077 / 31250000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (96747731 / 500000000) (193986037 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_5832.1) (by simpa only [div_one] using reflection_log_5833.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (96747731 / 1000000000) (193986037 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (96747731 / 1000000000) (193986037 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (5959 / 5000) (11919 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1919 / 10000) (-959 / 5000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8081 / 10000) (4041 / 5000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8081 / 10000) (4041 / 5000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1237317495669 / 1000000000000) (618735305037 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (737317495669 / 500000000000) (368735305037 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (737317495669 / 500000000000) (368735305037 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (77682099 / 200000000) (388618139 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_5834.1) (by simpa only [div_one] using reflection_log_5835.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (77682099 / 400000000) (388618139 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (77682099 / 400000000) (388618139 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1395639917 / 1000000000) (697843647 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (96447 / 1000000) (9669 / 100000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-93489561 / 10000000000) (-9302023809 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (13862909609 / 10000000000) (1386385270191 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (13862909609 / 10000000000) (1386385270191 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (954413347799 / 1000000000000) (190902182689 / 200000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (136776682683 / 100000000000) (683893137217 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (49069474539 / 50000000000) (981482480029 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (49069474539 / 50000000000) (981482480029 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (167788998711 / 125000000000) (671229132391 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1395639917 / 2000000000) (697843647 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (6086908681 / 12500000000) (486985755659 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339805309053 / 1000000000000) (339839915767 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339805309053 / 1000000000000) (339839915767 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456124740501 / 1000000000000) (3649767229 / 8000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2191920607 / 1000000000) (2192382721669 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (522999571159 / 250000000000) (1046326617141 / 500000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (522999571159 / 250000000000) (1046326617141 / 500000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-193986037 / 2000000000) (-96747731 / 1000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1395639917 / 1000000000) (697843647 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (96447 / 1000000) (9669 / 100000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-93489561 / 10000000000) (-9302023809 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (13862909609 / 10000000000) (1386385270191 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (13862909609 / 10000000000) (1386385270191 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-105054447 / 781250000) (-33530126243 / 250000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (201877872779 / 200000000000) (1009437183919 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (97352575979 / 1000000000000) (48801240657 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (97352575979 / 1000000000000) (48801240657 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (97352575979 / 500000000000) (48801240657 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (96447 / 500000) (9669 / 50000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-9669 / 50000) (-96447 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (662575979 / 500000000000) (577740657 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (662575979 / 500000000000) (577740657 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (45616063 / 50000000000) (1591072191 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-1335573709 / 10000000000) (-132529432781 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (136776682683 / 100000000000) (683893137217 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (49069474539 / 50000000000) (981482480029 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (49069474539 / 50000000000) (981482480029 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (167788998711 / 125000000000) (671229132391 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1395639917 / 2000000000) (697843647 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (6086908681 / 12500000000) (486985755659 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339805309053 / 1000000000000) (339839915767 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339805309053 / 1000000000000) (339839915767 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456124740501 / 1000000000000) (3649767229 / 8000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2191920607 / 1000000000) (2192382721669 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-292808872313 / 1000000000000) (-145246997373 / 500000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-292808872313 / 1000000000000) (-145246997373 / 500000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (96447 / 250000) (9669 / 25000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (201877872779 / 200000000000) (1009437183919 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (194705151959 / 500000000000) (390409925253 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (194705151959 / 500000000000) (390409925253 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (289341 / 1000000) (29007 / 100000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (345648035171 / 500000000000) (691352288781 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (289288114389 / 200000000000) (289311640237 / 200000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (418514561527 / 1000000000000) (209801568709 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (418514561527 / 1000000000000) (209801568709 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-209801568709 / 500000000000) (-418514561527 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-60385667 / 2000000000) (-14052318137 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-60385667 / 2000000000) (-14052318137 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-15795782669 / 250000000000) (-470358807 / 8000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-355992002989 / 1000000000000) (-349288845621 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1395639917 / 1000000000) (697843647 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (96447 / 1000000) (9669 / 100000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (9302023809 / 1000000000000) (93489561 / 10000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-93489561 / 10000000000) (-9302023809 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (13862909609 / 10000000000) (1386385270191 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (13862909609 / 10000000000) (1386385270191 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (26740720861 / 200000000000) (5361983671 / 40000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (9906510439 / 10000000000) (990697976191 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (49069474539 / 50000000000) (981482480029 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (49069474539 / 50000000000) (981482480029 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1395639917 / 2000000000) (697843647 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (6086908681 / 12500000000) (486985755659 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (6086908681 / 12500000000) (486985755659 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (477890256869 / 1000000000000) (477967987203 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2092190328167 / 1000000000000) (2092530629421 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (279733387767 / 1000000000000) (280502876651 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (279733387767 / 1000000000000) (280502876651 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (3746102701 / 200000000000) (1878774393 / 100000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (353597952023 / 500000000000) (707276675519 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (353597952023 / 500000000000) (707276675519 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (500126046699 / 1000000000000) (250120147867 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (500126046699 / 1000000000000) (250120147867 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-35616308971 / 200000000000) (-43672112379 / 250000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (522999571159 / 125000000000) (1046326617141 / 250000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (3746102701 / 200000000000) (1878774393 / 100000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (353597952023 / 500000000000) (707276675519 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2958905236331 / 1000000000000) (592033929023 / 200000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-193986037 / 2000000000) (-96747731 / 1000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (97212229 / 1000000000) (195122677 / 2000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (97212229 / 1000000000) (195122677 / 2000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (287641773423 / 1000000000000) (57759622553 / 200000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (13695028571 / 125000000000) (114109663249 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (959 / 5000) (1919 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (919681 / 25000000) (3682561 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (919681 / 25000000) (3682561 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3682561 / 100000000) (-919681 / 25000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96317439 / 100000000) (24080319 / 25000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96317439 / 100000000) (24080319 / 25000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (519096113303 / 500000000000) (519116792547 / 500000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (519096113303 / 500000000000) (519116792547 / 500000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (519096113303 / 500000000000) (519116792547 / 500000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (290417028701 / 1000000000000) (58245501451 / 200000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (399977257269 / 1000000000000) (50667146313 / 125000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (688465390541 / 1000000000000) (688488931589 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (118496148493 / 250000000000) (474017008921 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (118496148493 / 250000000000) (474017008921 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (47395764471 / 250000000000) (192136713167 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (1864169903 / 3906250000) (238625240517 / 500000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (1047667880641 / 500000000000) (83817467361 / 40000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (397240160917 / 1000000000000) (402610317119 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (397240160917 / 1000000000000) (402610317119 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (473208328343686861962106559 / 1159723526283522000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_418 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((959 / 5000):ℝ) ((1919 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (473208328343686861962106559 / 1159723526283522000000000000) := by
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
  have hsl : (958041 / 10000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1920919 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1919 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_418 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_418 {a z : ℝ}
    (ha : a ∈ Set.Icc ((959 / 5000):ℝ) ((1919 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_418 ha ⟨hz.1.le,hz.2⟩ hs) (M := (473208328343686861962106559 / 1159723526283522000000000000))
  exact lt_of_lt_of_le (by norm_num : (473208328343686861962106559 / 1159723526283522000000000000) < 2*((959 / 5000):ℝ)/(1-((959 / 5000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0419 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_419 (a z s c : ℝ)
    (ha : Bounds (1919 / 10000) (24 / 125) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1917081 / 20000000) (3003 / 31250) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (3787568269322977015573631861 / 9277049055518721000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(24 / 125)
  have hx1 : Bounds (149 / 125) (149 / 125) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24 / 125) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(24 / 125)
  have hx2 : Bounds (149 / 125) (149 / 125) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24 / 125) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (21954071 / 125000000) (175632569 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_5836.1) (by simpa only [div_one] using reflection_log_5836.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (3271156579 / 15625000000) (26169252781 / 125000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(24 / 125)
  have hx5 : Bounds (-24 / 125) (-24 / 125) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24 / 125) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (101 / 125) (101 / 125) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(24 / 125)
  have hx7 : Bounds (101 / 125) (101 / 125) x7 := by
    exact hx6
  let x8 : ℝ := -(24 / 125)
  have hx8 : Bounds (-24 / 125) (-24 / 125) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24 / 125) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (101 / 125) (101 / 125) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(24 / 125)
  have hx10 : Bounds (101 / 125) (101 / 125) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-213193221 / 1000000000) (-10659661 / 50000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_5837.1) (by simpa only [div_one] using reflection_log_5837.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-21532515321 / 125000000000) (-1076625761 / 6250000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (4636737311 / 125000000000) (4636737561 / 125000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (4636737311 / 250000000000) (4636737561 / 250000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (4636737311 / 250000000000) (4636737561 / 250000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-4636737561 / 250000000000) (-4636737311 / 250000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (168650057439 / 250000000000) (168650057939 / 250000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (168650057439 / 250000000000) (168650057939 / 250000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (24 / 125)
  have hx20 : Bounds (168650057439 / 250000000000) (168650057939 / 250000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1919 / 10000)
  have hx22 : Bounds (11919 / 10000) (11919 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1919 / 10000)
  have hx23 : Bounds (11919 / 10000) (11919 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (685737 / 3906250) (175548673 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_5822.1) (by simpa only [div_one] using reflection_log_5822.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (52309115539 / 250000000000) (209236463349 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1919 / 10000)
  have hx26 : Bounds (-1919 / 10000) (-1919 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8081 / 10000) (8081 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1919 / 10000)
  have hx28 : Bounds (8081 / 10000) (8081 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1919 / 10000)
  have hx29 : Bounds (-1919 / 10000) (-1919 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8081 / 10000) (8081 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1919 / 10000)
  have hx31 : Bounds (8081 / 10000) (8081 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-106534733 / 500000000) (-42613893 / 200000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_5823.1) (by simpa only [div_one] using reflection_log_5823.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-6887257419 / 40000000000) (-86090717333 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (37055026681 / 1000000000000) (37055028683 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (926375667 / 50000000000) (9263757171 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (926375667 / 50000000000) (9263757171 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-9263757171 / 500000000000) (-926375667 / 50000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (337309832829 / 500000000000) (33730983383 / 50000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (337309832829 / 500000000000) (33730983383 / 50000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1919 / 10000)
  have hx41 : Bounds (337309832829 / 500000000000) (33730983383 / 50000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (168650057439 / 250000000000) (33730983383 / 50000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (3 / 15625) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(3 / 15625)
  have hx45 : Bounds (15628 / 15625) (15628 / 15625) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3 / 15625) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(3 / 15625)
  have hx46 : Bounds (15628 / 15625) (15628 / 15625) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3 / 15625) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (191981 / 1000000000) (95991 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5838.1) (by simpa only [div_one] using reflection_log_5838.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (9600893 / 50000000000) (192018861 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(3 / 15625)
  have hx49 : Bounds (-3 / 15625) (-3 / 15625) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3 / 15625) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (15622 / 15625) (15622 / 15625) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(3 / 15625)
  have hx51 : Bounds (15622 / 15625) (15622 / 15625) x51 := by
    exact hx50
  let x52 : ℝ := -(3 / 15625)
  have hx52 : Bounds (-3 / 15625) (-3 / 15625) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3 / 15625) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (15622 / 15625) (15622 / 15625) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(3 / 15625)
  have hx54 : Bounds (15622 / 15625) (15622 / 15625) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-192019 / 1000000000) (-96009 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_5839.1) (by simpa only [div_one] using reflection_log_5839.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-191982133 / 1000000000000) (-47995283 / 250000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (35727 / 1000000000000) (37729 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (17863 / 1000000000000) (3773 / 200000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (17863 / 1000000000000) (3773 / 200000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-3773 / 200000000000) (-17863 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (138629432227 / 200000000000) (693147163137 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (138629432227 / 200000000000) (693147163137 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (3 / 15625)
  have hx64 : Bounds (138629432227 / 200000000000) (693147163137 / 1000000000000) x64 := by
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
  have hx86 : Bounds (138629432227 / 200000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1367747390891 / 1000000000000) (68388342433 / 50000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (136774739089 / 200000000000) (68388342433 / 100000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (136774739089 / 200000000000) (68388342433 / 100000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (520313020313 / 50000000000) (652032960527 / 62500000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (444785484987 / 62500000000) (356731627057 / 50000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (444785484987 / 62500000000) (356731627057 / 50000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(48249 / 500000)
  have hx95 : Bounds (548249 / 500000) (548249 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48249 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(48249 / 500000)
  have hx96 : Bounds (548249 / 500000) (548249 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48249 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (11515183 / 125000000) (18424293 / 200000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_5840.1) (by simpa only [div_one] using reflection_log_5840.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (101011001033 / 1000000000000) (10101100213 / 100000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(48249 / 500000)
  have hx99 : Bounds (-48249 / 500000) (-48249 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48249 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (451751 / 500000) (451751 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(48249 / 500000)
  have hx101 : Bounds (451751 / 500000) (451751 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(48249 / 500000)
  have hx102 : Bounds (-48249 / 500000) (-48249 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48249 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (451751 / 500000) (451751 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(48249 / 500000)
  have hx104 : Bounds (451751 / 500000) (451751 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-25369239 / 250000000) (-20295391 / 200000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_5841.1) (by simpa only [div_one] using reflection_log_5841.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-916846327 / 10000000000) (-22921157949 / 250000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (9326368333 / 1000000000000) (4663185167 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (2331592083 / 500000000000) (4663185167 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (2331592083 / 500000000000) (4663185167 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4663185167 / 1000000000000) (-2331592083 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688483994833 / 1000000000000) (344241998417 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688483994833 / 1000000000000) (344241998417 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (48249 / 500000)
  have hx114 : Bounds (688483994833 / 1000000000000) (344241998417 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(96741 / 1000000)
  have hx116 : Bounds (1096741 / 1000000) (1096741 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96741 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(96741 / 1000000)
  have hx117 : Bounds (1096741 / 1000000) (1096741 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96741 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (46171527 / 500000000) (18468611 / 200000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_5842.1) (by simpa only [div_one] using reflection_log_5842.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (101276413387 / 1000000000000) (25319103621 / 250000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(96741 / 1000000)
  have hx120 : Bounds (-96741 / 1000000) (-96741 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96741 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (903259 / 1000000) (903259 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(96741 / 1000000)
  have hx122 : Bounds (903259 / 1000000) (903259 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(96741 / 1000000)
  have hx123 : Bounds (-96741 / 1000000) (-96741 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96741 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (903259 / 1000000) (903259 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(96741 / 1000000)
  have hx125 : Bounds (903259 / 1000000) (903259 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-20349189 / 200000000) (-12718243 / 125000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_5843.1) (by simpa only [div_one] using reflection_log_5843.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-18380588107 / 200000000000) (-91902939631 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (2343368213 / 250000000000) (9373474853 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2343368213 / 500000000000) (4686737427 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2343368213 / 500000000000) (4686737427 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4686737427 / 1000000000000) (-2343368213 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (688460442573 / 1000000000000) (344230222287 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (688460442573 / 1000000000000) (344230222287 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (96741 / 1000000)
  have hx135 : Bounds (688460442573 / 1000000000000) (344230222287 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(48249 / 500000)
  have hx136 : Bounds (171683638921 / 250000000000) (137695554191 / 200000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((48249 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(96741 / 1000000)
  have hx137 : Bounds (13769277633 / 20000000000) (690211486663 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((96741 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (48249 / 500000) (96741 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(48249 / 500000) ≤ (137695554191 / 200000000000) := hx136.2
      have h2 : (688483994833 / 1000000000000) ≤ biasE (48249 / 500000) := hx114.1
      linarith
    · have h1 : biasE (96741 / 1000000) ≤ (344230222287 / 500000000000) := hx135.2
      have h2 : (13769277633 / 20000000000) ≤ x93*(96741 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(96741 / 1000000)
  have hx139 : Bounds (1096741 / 1000000) (1096741 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96741 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(96741 / 1000000)
  have hx140 : Bounds (1096741 / 1000000) (1096741 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96741 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (46171527 / 500000000) (18468611 / 200000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_5842.1) (by simpa only [div_one] using reflection_log_5842.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (101276413387 / 1000000000000) (25319103621 / 250000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(96741 / 1000000)
  have hx143 : Bounds (-96741 / 1000000) (-96741 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96741 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (903259 / 1000000) (903259 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(96741 / 1000000)
  have hx145 : Bounds (903259 / 1000000) (903259 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(96741 / 1000000)
  have hx146 : Bounds (-96741 / 1000000) (-96741 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96741 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (903259 / 1000000) (903259 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(96741 / 1000000)
  have hx148 : Bounds (903259 / 1000000) (903259 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-20349189 / 200000000) (-12718243 / 125000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_5843.1) (by simpa only [div_one] using reflection_log_5843.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-18380588107 / 200000000000) (-91902939631 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (2343368213 / 250000000000) (9373474853 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (2343368213 / 500000000000) (4686737427 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (2343368213 / 500000000000) (4686737427 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4686737427 / 1000000000000) (-2343368213 / 500000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (688460442573 / 1000000000000) (344230222287 / 500000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (688460442573 / 1000000000000) (344230222287 / 500000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (96741 / 1000000)
  have hx158 : Bounds (688460442573 / 1000000000000) (344230222287 / 500000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(48249 / 500000)
  have hx160 : Bounds (548249 / 500000) (548249 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48249 / 500000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(48249 / 500000)
  have hx161 : Bounds (548249 / 500000) (548249 / 500000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48249 / 500000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (11515183 / 125000000) (18424293 / 200000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_5840.1) (by simpa only [div_one] using reflection_log_5840.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (101011001033 / 1000000000000) (10101100213 / 100000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(48249 / 500000)
  have hx164 : Bounds (-48249 / 500000) (-48249 / 500000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48249 / 500000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (451751 / 500000) (451751 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(48249 / 500000)
  have hx166 : Bounds (451751 / 500000) (451751 / 500000) x166 := by
    exact hx165
  let x167 : ℝ := -(48249 / 500000)
  have hx167 : Bounds (-48249 / 500000) (-48249 / 500000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48249 / 500000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (451751 / 500000) (451751 / 500000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(48249 / 500000)
  have hx169 : Bounds (451751 / 500000) (451751 / 500000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-25369239 / 250000000) (-20295391 / 200000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_5841.1) (by simpa only [div_one] using reflection_log_5841.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-916846327 / 10000000000) (-22921157949 / 250000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (9326368333 / 1000000000000) (4663185167 / 500000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (2331592083 / 500000000000) (4663185167 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (2331592083 / 500000000000) (4663185167 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4663185167 / 1000000000000) (-2331592083 / 500000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688483994833 / 1000000000000) (344241998417 / 500000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688483994833 / 1000000000000) (344241998417 / 500000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (48249 / 500000)
  have hx179 : Bounds (688483994833 / 1000000000000) (344241998417 / 500000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (688460442573 / 1000000000000) (344241998417 / 500000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-9358821081 / 1000000000000) (-2327966001 / 250000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-9402891 / 1000000000) (-935549 / 100000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_5844.1) (by simpa only [div_one] using reflection_log_5845.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-9402891 / 2000000000) (-935549 / 200000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-9402891 / 2000000000) (-935549 / 200000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (935549 / 200000000) (9402891 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (27912997 / 40000000) (1395697253 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (27912997 / 40000000) (1395697253 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (48249 / 500000) (96741 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-9358821081 / 1000000000000) (-2327966001 / 250000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (548249 / 500000) (1096741 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-96741 / 1000000) (-48249 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (903259 / 1000000) (451751 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (903259 / 1000000) (451751 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (221360882433 / 200000000000) (1107102171139 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (121360882433 / 100000000000) (607102171139 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (121360882433 / 100000000000) (607102171139 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (9679921 / 50000000) (194089 / 1000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_5846.1) (by simpa only [div_one] using reflection_log_5847.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (9679921 / 100000000) (194089 / 2000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (9679921 / 100000000) (194089 / 2000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11919 / 10000) (149 / 125) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-24 / 125) (-1919 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (101 / 125) (8081 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (101 / 125) (8081 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1237470610073 / 1000000000000) (1237623762377 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (737470610073 / 500000000000) (737623762377 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (737470610073 / 500000000000) (737623762377 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (194309069 / 500000000) (38882579 / 100000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_5848.1) (by simpa only [div_one] using reflection_log_5849.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (194309069 / 1000000000) (38882579 / 200000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (194309069 / 1000000000) (38882579 / 200000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (27912997 / 20000000) (1395697253 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (48249 / 500000) (96741 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-9358821081 / 1000000000000) (-2327966001 / 250000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386291028919 / 1000000000000) (346596347249 / 250000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386291028919 / 1000000000000) (346596347249 / 250000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (119300816913 / 125000000000) (954504153769 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (136774739089 / 100000000000) (68388342433 / 50000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (98136994537 / 100000000000) (245365745701 / 250000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (98136994537 / 100000000000) (245365745701 / 250000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1342266182277 / 1000000000000) (1342412531067 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (27912997 / 40000000) (1395697253 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (486959625951 / 1000000000000) (121748176377 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339812564457 / 1000000000000) (67969438131 / 200000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339812564457 / 1000000000000) (67969438131 / 200000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456118913583 / 1000000000000) (57026890923 / 125000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2191948359393 / 1000000000000) (2192410729353 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2092009839253 / 1000000000000) (65395785873 / 31250000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2092009839253 / 1000000000000) (65395785873 / 31250000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-194089 / 2000000) (-9679921 / 100000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (27912997 / 20000000) (1395697253 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (48249 / 500000) (96741 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-9358821081 / 1000000000000) (-2327966001 / 250000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386291028919 / 1000000000000) (346596347249 / 250000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386291028919 / 1000000000000) (346596347249 / 250000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-134541076883 / 1000000000000) (-134191876429 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1009399389843 / 1000000000000) (504723618037 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (97405022321 / 1000000000000) (48827467533 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (97405022321 / 1000000000000) (48827467533 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (97405022321 / 500000000000) (48827467533 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (48249 / 250000) (96741 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-96741 / 500000) (-48249 / 250000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (664022321 / 500000000000) (578467533 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (664022321 / 500000000000) (578467533 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (914306201 / 1000000000000) (1593062557 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-66813385341 / 500000000000) (-8287425867 / 62500000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (136774739089 / 100000000000) (68388342433 / 50000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (98136994537 / 100000000000) (245365745701 / 250000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (98136994537 / 100000000000) (245365745701 / 250000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1342266182277 / 1000000000000) (1342412531067 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (27912997 / 40000000) (1395697253 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (486959625951 / 1000000000000) (121748176377 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339812564457 / 1000000000000) (67969438131 / 200000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339812564457 / 1000000000000) (67969438131 / 200000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456118913583 / 1000000000000) (57026890923 / 125000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2191948359393 / 1000000000000) (2192410729353 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-292964765773 / 1000000000000) (-72662438131 / 250000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-292964765773 / 1000000000000) (-72662438131 / 250000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (48249 / 125000) (96741 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1009399389843 / 1000000000000) (504723618037 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (97405022321 / 250000000000) (390619740261 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (97405022321 / 250000000000) (390619740261 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (144747 / 500000) (290223 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691294106381 / 1000000000000) (138270070999 / 200000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (361611154451 / 250000000000) (289312462169 / 200000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (209368519093 / 500000000000) (419825653541 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (209368519093 / 500000000000) (419825653541 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-419825653541 / 1000000000000) (-209368519093 / 500000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-30205564257 / 1000000000000) (-1124691917 / 40000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-30205564257 / 1000000000000) (-1124691917 / 40000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-12642026319 / 200000000000) (-7352707989 / 125000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-44521862171 / 125000000000) (-87367854109 / 250000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (27912997 / 20000000) (1395697253 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (48249 / 500000) (96741 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (2327966001 / 250000000000) (9358821081 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-9358821081 / 1000000000000) (-2327966001 / 250000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386291028919 / 1000000000000) (346596347249 / 250000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386291028919 / 1000000000000) (346596347249 / 250000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (33443577927 / 250000000000) (134120308917 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (990641178919 / 1000000000000) (247672033999 / 250000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (98136994537 / 100000000000) (245365745701 / 250000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (98136994537 / 100000000000) (245365745701 / 250000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (27912997 / 40000000) (1395697253 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (486959625951 / 1000000000000) (121748176377 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (486959625951 / 1000000000000) (121748176377 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (119471885379 / 250000000000) (59745664169 / 125000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (16737616259 / 8000000000) (1046271259581 / 500000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (55976577367 / 200000000000) (70163112273 / 250000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (55976577367 / 200000000000) (70163112273 / 250000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (937521827 / 50000000000) (4701924469 / 250000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (707210879113 / 1000000000000) (70729169471 / 100000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (707210879113 / 1000000000000) (70729169471 / 100000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (100029445507 / 200000000000) (250130770703 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (100029445507 / 200000000000) (250130770703 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-5568143849 / 31250000000) (-174787160033 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2092009839253 / 500000000000) (65395785873 / 15625000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (937521827 / 50000000000) (4701924469 / 250000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (707210879113 / 1000000000000) (70729169471 / 100000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1479492117531 / 500000000000) (2960249357889 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-194089 / 2000000) (-9679921 / 100000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (97264569 / 1000000000) (19522737 / 200000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (97264569 / 1000000000) (19522737 / 200000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (287804326301 / 1000000000000) (288960848343 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (109623723133 / 1000000000000) (11417368831 / 100000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1919 / 10000) (24 / 125) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3682561 / 100000000) (576 / 15625) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3682561 / 100000000) (576 / 15625) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-576 / 15625) (-3682561 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (15049 / 15625) (96317439 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (15049 / 15625) (96317439 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1038233585093 / 1000000000000) (1038274968437 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1038233585093 / 1000000000000) (1038274968437 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1038233585093 / 1000000000000) (1038274968437 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (72645953251 / 250000000000) (291394412723 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (400207536137 / 1000000000000) (405568101033 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (688460442573 / 1000000000000) (344241998417 / 500000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (473977780987 / 1000000000000) (474010213897 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (473977780987 / 1000000000000) (474010213897 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (23711184989 / 125000000000) (192243422321 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477224110233 / 1000000000000) (95449421671 / 200000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (419070113781 / 200000000000) (2095451546889 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (12420811239 / 31250000000) (201418388341 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (12420811239 / 31250000000) (201418388341 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (3787568269322977015573631861 / 9277049055518721000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_419 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1919 / 10000):ℝ) ((24 / 125)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (3787568269322977015573631861 / 9277049055518721000000000000) := by
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
  have hsl : (1917081 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (3003 / 31250) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (24 / 125))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_419 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_419 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1919 / 10000):ℝ) ((24 / 125)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_419 ha ⟨hz.1.le,hz.2⟩ hs) (M := (3787568269322977015573631861 / 9277049055518721000000000000))
  exact lt_of_lt_of_le (by norm_num : (3787568269322977015573631861 / 9277049055518721000000000000) < 2*((1919 / 10000):ℝ)/(1-((1919 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0420 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_420 (a z s c : ℝ)
    (ha : Bounds (24 / 125) (1921 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (2997 / 31250) (1922921 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (92516352599815089303 / 226472401000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1921 / 10000)
  have hx1 : Bounds (11921 / 10000) (11921 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1921 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1921 / 10000)
  have hx2 : Bounds (11921 / 10000) (11921 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1921 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (175716457 / 1000000000) (87858229 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_5850.1) (by simpa only [div_one] using reflection_log_5850.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (209471588389 / 1000000000000) (104735794791 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1921 / 10000)
  have hx5 : Bounds (-1921 / 10000) (-1921 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1921 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8079 / 10000) (8079 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1921 / 10000)
  have hx7 : Bounds (8079 / 10000) (8079 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1921 / 10000)
  have hx8 : Bounds (-1921 / 10000) (-1921 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1921 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8079 / 10000) (8079 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1921 / 10000)
  have hx10 : Bounds (8079 / 10000) (8079 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-213316991 / 1000000000) (-21331699 / 100000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_5851.1) (by simpa only [div_one] using reflection_log_5851.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-172338797029 / 1000000000000) (-172338796221 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (116039973 / 3125000000) (37132793361 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (116039973 / 6250000000) (18566396681 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (116039973 / 6250000000) (18566396681 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18566396681 / 1000000000000) (-116039973 / 6250000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674580783319 / 1000000000000) (16864519633 / 25000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674580783319 / 1000000000000) (16864519633 / 25000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1921 / 10000)
  have hx20 : Bounds (674580783319 / 1000000000000) (16864519633 / 25000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(24 / 125)
  have hx22 : Bounds (149 / 125) (149 / 125) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24 / 125) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(24 / 125)
  have hx23 : Bounds (149 / 125) (149 / 125) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24 / 125) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (21954071 / 125000000) (175632569 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_5836.1) (by simpa only [div_one] using reflection_log_5836.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (3271156579 / 15625000000) (26169252781 / 125000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(24 / 125)
  have hx26 : Bounds (-24 / 125) (-24 / 125) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24 / 125) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (101 / 125) (101 / 125) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(24 / 125)
  have hx28 : Bounds (101 / 125) (101 / 125) x28 := by
    exact hx27
  let x29 : ℝ := -(24 / 125)
  have hx29 : Bounds (-24 / 125) (-24 / 125) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24 / 125) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (101 / 125) (101 / 125) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(24 / 125)
  have hx31 : Bounds (101 / 125) (101 / 125) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-213193221 / 1000000000) (-10659661 / 50000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_5837.1) (by simpa only [div_one] using reflection_log_5837.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-21532515321 / 125000000000) (-1076625761 / 6250000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (4636737311 / 125000000000) (4636737561 / 125000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (4636737311 / 250000000000) (4636737561 / 250000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (4636737311 / 250000000000) (4636737561 / 250000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-4636737561 / 250000000000) (-4636737311 / 250000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (168650057439 / 250000000000) (168650057939 / 250000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (168650057439 / 250000000000) (168650057939 / 250000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (24 / 125)
  have hx41 : Bounds (168650057439 / 250000000000) (168650057939 / 250000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674580783319 / 1000000000000) (168650057939 / 250000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1921 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1921 / 10000000)
  have hx45 : Bounds (10001921 / 10000000) (10001921 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1921 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1921 / 10000000)
  have hx46 : Bounds (10001921 / 10000000) (10001921 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1921 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (192081 / 1000000000) (96041 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5852.1) (by simpa only [div_one] using reflection_log_5852.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (96058949 / 500000000000) (192118899 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1921 / 10000000)
  have hx49 : Bounds (-1921 / 10000000) (-1921 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1921 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998079 / 10000000) (9998079 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1921 / 10000000)
  have hx51 : Bounds (9998079 / 10000000) (9998079 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1921 / 10000000)
  have hx52 : Bounds (-1921 / 10000000) (-1921 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1921 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998079 / 10000000) (9998079 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1921 / 10000000)
  have hx54 : Bounds (9998079 / 10000000) (9998079 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-192119 / 1000000000) (-96059 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_5853.1) (by simpa only [div_one] using reflection_log_5853.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-96041047 / 500000000000) (-96040547 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (8951 / 250000000000) (7561 / 200000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (8951 / 500000000000) (18903 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (8951 / 500000000000) (18903 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-18903 / 1000000000000) (-8951 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147161097 / 1000000000000) (346573581549 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147161097 / 1000000000000) (346573581549 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1921 / 10000000)
  have hx64 : Bounds (693147161097 / 1000000000000) (346573581549 / 500000000000) x64 := by
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
  have hx86 : Bounds (693147161097 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (42741498263 / 31250000000) (341936853189 / 250000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (42741498263 / 62500000000) (341936853189 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (42741498263 / 62500000000) (341936853189 / 500000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (5200421650187 / 500000000000) (2606773440107 / 250000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (3556381006853 / 500000000000) (1426163051339 / 200000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (3556381006853 / 500000000000) (1426163051339 / 200000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(96549 / 1000000)
  have hx95 : Bounds (1096549 / 1000000) (1096549 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96549 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(96549 / 1000000)
  have hx96 : Bounds (1096549 / 1000000) (1096549 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96549 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (3686719 / 40000000) (11520997 / 125000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_5854.1) (by simpa only [div_one] using reflection_log_5854.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (50533350409 / 500000000000) (20213340383 / 200000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(96549 / 1000000)
  have hx99 : Bounds (-96549 / 1000000) (-96549 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96549 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (903451 / 1000000) (903451 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(96549 / 1000000)
  have hx101 : Bounds (903451 / 1000000) (903451 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(96549 / 1000000)
  have hx102 : Bounds (-96549 / 1000000) (-96549 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96549 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (903451 / 1000000) (903451 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(96549 / 1000000)
  have hx104 : Bounds (903451 / 1000000) (903451 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-25383351 / 250000000) (-101533403 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_5855.1) (by simpa only [div_one] using reflection_log_5855.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-45865227689 / 500000000000) (-91730454473 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (29175767 / 3125000000) (4668123721 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (29175767 / 6250000000) (4668123721 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (29175767 / 6250000000) (4668123721 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4668123721 / 1000000000000) (-29175767 / 6250000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688479056279 / 1000000000000) (17211976457 / 25000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688479056279 / 1000000000000) (17211976457 / 25000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (96549 / 1000000)
  have hx114 : Bounds (688479056279 / 1000000000000) (17211976457 / 25000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(12099 / 125000)
  have hx116 : Bounds (137099 / 125000) (137099 / 125000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12099 / 125000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(12099 / 125000)
  have hx117 : Bounds (137099 / 125000) (137099 / 125000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12099 / 125000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (18477911 / 200000000) (23097389 / 250000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_5856.1) (by simpa only [div_one] using reflection_log_5856.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (101332124807 / 1000000000000) (20266425181 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(12099 / 125000)
  have hx120 : Bounds (-12099 / 125000) (-12099 / 125000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12099 / 125000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (112901 / 125000) (112901 / 125000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(12099 / 125000)
  have hx122 : Bounds (112901 / 125000) (112901 / 125000) x122 := by
    exact hx121
  let x123 : ℝ := -(12099 / 125000)
  have hx123 : Bounds (-12099 / 125000) (-12099 / 125000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12099 / 125000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (112901 / 125000) (112901 / 125000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(12099 / 125000)
  have hx125 : Bounds (112901 / 125000) (112901 / 125000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-101802409 / 1000000000) (-12725301 / 125000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_5857.1) (by simpa only [div_one] using reflection_log_5857.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-91948750229 / 1000000000000) (-22987187331 / 250000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4691687289 / 500000000000) (9383376581 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4691687289 / 1000000000000) (4691688291 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4691687289 / 1000000000000) (4691688291 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4691688291 / 1000000000000) (-4691687289 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (688455491709 / 1000000000000) (688455493711 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (688455491709 / 1000000000000) (688455493711 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (12099 / 125000)
  have hx135 : Bounds (688455491709 / 1000000000000) (688455493711 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(96549 / 1000000)
  have hx136 : Bounds (686730059661 / 1000000000000) (688473082219 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((96549 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(12099 / 125000)
  have hx137 : Bounds (68845846083 / 100000000000) (690205870327 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((12099 / 125000) : ℝ)) <;> norm_num
  have hc : Bounds (96549 / 1000000) (12099 / 125000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(96549 / 1000000) ≤ (688473082219 / 1000000000000) := hx136.2
      have h2 : (688479056279 / 1000000000000) ≤ biasE (96549 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (12099 / 125000) ≤ (688455493711 / 1000000000000) := hx135.2
      have h2 : (68845846083 / 100000000000) ≤ x93*(12099 / 125000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(12099 / 125000)
  have hx139 : Bounds (137099 / 125000) (137099 / 125000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12099 / 125000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(12099 / 125000)
  have hx140 : Bounds (137099 / 125000) (137099 / 125000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12099 / 125000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (18477911 / 200000000) (23097389 / 250000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_5856.1) (by simpa only [div_one] using reflection_log_5856.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (101332124807 / 1000000000000) (20266425181 / 200000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(12099 / 125000)
  have hx143 : Bounds (-12099 / 125000) (-12099 / 125000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12099 / 125000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (112901 / 125000) (112901 / 125000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(12099 / 125000)
  have hx145 : Bounds (112901 / 125000) (112901 / 125000) x145 := by
    exact hx144
  let x146 : ℝ := -(12099 / 125000)
  have hx146 : Bounds (-12099 / 125000) (-12099 / 125000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12099 / 125000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (112901 / 125000) (112901 / 125000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(12099 / 125000)
  have hx148 : Bounds (112901 / 125000) (112901 / 125000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-101802409 / 1000000000) (-12725301 / 125000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_5857.1) (by simpa only [div_one] using reflection_log_5857.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-91948750229 / 1000000000000) (-22987187331 / 250000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (4691687289 / 500000000000) (9383376581 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4691687289 / 1000000000000) (4691688291 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4691687289 / 1000000000000) (4691688291 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4691688291 / 1000000000000) (-4691687289 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (688455491709 / 1000000000000) (688455493711 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (688455491709 / 1000000000000) (688455493711 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (12099 / 125000)
  have hx158 : Bounds (688455491709 / 1000000000000) (688455493711 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(96549 / 1000000)
  have hx160 : Bounds (1096549 / 1000000) (1096549 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96549 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(96549 / 1000000)
  have hx161 : Bounds (1096549 / 1000000) (1096549 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96549 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (3686719 / 40000000) (11520997 / 125000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_5854.1) (by simpa only [div_one] using reflection_log_5854.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (50533350409 / 500000000000) (20213340383 / 200000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(96549 / 1000000)
  have hx164 : Bounds (-96549 / 1000000) (-96549 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96549 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (903451 / 1000000) (903451 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(96549 / 1000000)
  have hx166 : Bounds (903451 / 1000000) (903451 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(96549 / 1000000)
  have hx167 : Bounds (-96549 / 1000000) (-96549 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96549 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (903451 / 1000000) (903451 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(96549 / 1000000)
  have hx169 : Bounds (903451 / 1000000) (903451 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-25383351 / 250000000) (-101533403 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_5855.1) (by simpa only [div_one] using reflection_log_5855.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-45865227689 / 500000000000) (-91730454473 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (29175767 / 3125000000) (4668123721 / 500000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (29175767 / 6250000000) (4668123721 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (29175767 / 6250000000) (4668123721 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4668123721 / 1000000000000) (-29175767 / 6250000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688479056279 / 1000000000000) (17211976457 / 25000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688479056279 / 1000000000000) (17211976457 / 25000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (96549 / 1000000)
  have hx179 : Bounds (688479056279 / 1000000000000) (17211976457 / 25000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (688455491709 / 1000000000000) (17211976457 / 25000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-146385801 / 15625000000) (-9321709401 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4706427 / 500000000) (-2341357 / 250000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_5858.1) (by simpa only [div_one] using reflection_log_5859.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4706427 / 1000000000) (-2341357 / 500000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4706427 / 1000000000) (-2341357 / 500000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (2341357 / 500000000) (4706427 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (348914947 / 500000000) (87231701 / 125000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (348914947 / 500000000) (87231701 / 125000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (96549 / 1000000) (12099 / 125000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-146385801 / 15625000000) (-9321709401 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1096549 / 1000000) (137099 / 125000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-12099 / 125000) (-96549 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (112901 / 125000) (903451 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (112901 / 125000) (903451 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (276716722877 / 250000000000) (138395585513 / 125000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (151716722877 / 125000000000) (75895585513 / 62500000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (151716722877 / 125000000000) (75895585513 / 62500000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (193701379 / 1000000000) (38838393 / 200000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_5860.1) (by simpa only [div_one] using reflection_log_5861.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (193701379 / 2000000000) (38838393 / 400000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (193701379 / 2000000000) (38838393 / 400000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (149 / 125) (11921 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1921 / 10000) (-24 / 125) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8079 / 10000) (101 / 125) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8079 / 10000) (101 / 125) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (154702970297 / 125000000000) (618888476297 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (92202970297 / 62500000000) (368888476297 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (92202970297 / 62500000000) (368888476297 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (388825789 / 1000000000) (389033449 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_5862.1) (by simpa only [div_one] using reflection_log_5863.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (388825789 / 2000000000) (389033449 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (388825789 / 2000000000) (389033449 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (348914947 / 250000000) (87231701 / 62500000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (96549 / 1000000) (12099 / 125000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-146385801 / 15625000000) (-9321709401 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (43321596773 / 31250000000) (1386385506599 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (43321596773 / 31250000000) (1386385506599 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (190879943731 / 200000000000) (954497387997 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (42741498263 / 31250000000) (341936853189 / 250000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (122668798731 / 125000000000) (196288695093 / 200000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (122668798731 / 125000000000) (196288695093 / 200000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (671110175729 / 500000000000) (671183387167 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (348914947 / 500000000) (87231701 / 125000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (1521770503 / 3125000000) (486999658199 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (663710593 / 1953125000) (339854468569 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (663710593 / 1953125000) (339854468569 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (228056541543 / 500000000000) (114052336679 / 250000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (3424962709 / 1562500000) (548109688739 / 250000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2092021405359 / 1000000000000) (2092677064949 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2092021405359 / 1000000000000) (2092677064949 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-38838393 / 400000000) (-193701379 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (348914947 / 250000000) (87231701 / 62500000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (96549 / 1000000) (12099 / 125000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-146385801 / 15625000000) (-9321709401 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (43321596773 / 31250000000) (1386385506599 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (43321596773 / 31250000000) (1386385506599 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-134612462887 / 1000000000000) (-67131624283 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1009409421291 / 1000000000000) (100945729373 / 100000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (12182183777 / 125000000000) (781659123 / 8000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (12182183777 / 125000000000) (781659123 / 8000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (12182183777 / 62500000000) (781659123 / 4000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (96549 / 500000) (12099 / 62500) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-12099 / 62500) (-96549 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (83183777 / 62500000000) (9267123 / 4000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (83183777 / 62500000000) (9267123 / 4000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (916293249 / 1000000000000) (159505503 / 100000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-66848084819 / 500000000000) (-518235131 / 3906250000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (42741498263 / 31250000000) (341936853189 / 250000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (122668798731 / 125000000000) (196288695093 / 200000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (122668798731 / 125000000000) (196288695093 / 200000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (671110175729 / 500000000000) (671183387167 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (348914947 / 500000000) (87231701 / 125000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (1521770503 / 3125000000) (486999658199 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (663710593 / 1953125000) (339854468569 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (663710593 / 1953125000) (339854468569 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (228056541543 / 500000000000) (114052336679 / 250000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (3424962709 / 1562500000) (548109688739 / 250000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-36640082963 / 125000000000) (-290805513939 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-36640082963 / 125000000000) (-290805513939 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (96549 / 250000) (12099 / 31250) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1009409421291 / 1000000000000) (100945729373 / 100000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (12182183777 / 31250000000) (390829561499 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (12182183777 / 31250000000) (390829561499 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (289647 / 1000000) (36297 / 125000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (43205758823 / 62500000000) (345674209731 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (723224333671 / 500000000000) (1446566423149 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (418959517149 / 1000000000000) (420048171689 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (418959517149 / 1000000000000) (420048171689 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-420048171689 / 1000000000000) (-418959517149 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-1208731633 / 40000000000) (-562599113 / 20000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-1208731633 / 40000000000) (-562599113 / 20000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-7904640519 / 125000000000) (-58848469351 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-22272361741 / 62500000000) (-34965398329 / 100000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (348914947 / 250000000) (87231701 / 62500000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (96549 / 1000000) (12099 / 125000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (9321709401 / 1000000000000) (146385801 / 15625000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-146385801 / 15625000000) (-9321709401 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (43321596773 / 31250000000) (1386385506599 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (43321596773 / 31250000000) (1386385506599 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (66922509549 / 500000000000) (26838205191 / 200000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (15478614199 / 15625000000) (990678290599 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (122668798731 / 125000000000) (196288695093 / 200000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (122668798731 / 125000000000) (196288695093 / 200000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (348914947 / 500000000) (87231701 / 125000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (1521770503 / 3125000000) (486999658199 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (1521770503 / 3125000000) (486999658199 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (477884824441 / 1000000000000) (238981318547 / 500000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (8368854989 / 4000000000) (2092554416579 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (280032388957 / 1000000000000) (70200506007 / 250000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (280032388957 / 1000000000000) (70200506007 / 250000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (18770370551 / 1000000000000) (9413831399 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (35361293113 / 50000000000) (353653360539 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (35361293113 / 50000000000) (353653360539 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (500168420249 / 1000000000000) (500282797683 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (500168420249 / 1000000000000) (500282797683 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-35655934217 / 200000000000) (-34977176091 / 200000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2092021405359 / 500000000000) (2092677064949 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (18770370551 / 1000000000000) (9413831399 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (35361293113 / 50000000000) (353653360539 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1479531642271 / 500000000000) (2960329106169 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-38838393 / 400000000) (-193701379 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (6082307 / 62500000) (19533207 / 200000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (6082307 / 62500000) (19533207 / 200000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (17997931329 / 62500000000) (57824721219 / 200000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (109687230179 / 1000000000000) (2855943141 / 25000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (24 / 125) (1921 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (576 / 15625) (3690241 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (576 / 15625) (3690241 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3690241 / 100000000) (-576 / 15625) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96309759 / 100000000) (15049 / 15625) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96309759 / 100000000) (15049 / 15625) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (259568742109 / 250000000000) (1038316376641 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (259568742109 / 250000000000) (1038316376641 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (259568742109 / 250000000000) (1038316376641 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (58150123961 / 200000000000) (291561340143 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (3128420703 / 7812500000) (405799065783 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (688455491709 / 1000000000000) (17211976457 / 25000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (14811592627 / 31250000000) (474003413691 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (14811592627 / 31250000000) (474003413691 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (47448978451 / 250000000000) (96175071227 / 500000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (119305180809 / 250000000000) (477243733413 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (130960336667 / 62500000000) (2095466419017 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (99422947079 / 250000000000) (201531632103 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (99422947079 / 250000000000) (201531632103 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (92516352599815089303 / 226472401000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_420 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((24 / 125):ℝ) ((1921 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (92516352599815089303 / 226472401000000000000) := by
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
  have hsl : (2997 / 31250) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1922921 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1921 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_420 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_420 {a z : ℝ}
    (ha : a ∈ Set.Icc ((24 / 125):ℝ) ((1921 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_420 ha ⟨hz.1.le,hz.2⟩ hs) (M := (92516352599815089303 / 226472401000000000000))
  exact lt_of_lt_of_le (by norm_num : (92516352599815089303 / 226472401000000000000) < 2*((24 / 125):ℝ)/(1-((24 / 125):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end


