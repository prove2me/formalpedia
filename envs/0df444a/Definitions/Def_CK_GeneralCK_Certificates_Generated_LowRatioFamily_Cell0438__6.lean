-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0438__6
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0438__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:37:47.812636+00:00
-- url     : https://prove2.me/theorems/afd5d2ff-73f2-46d5-a7ef-016b71eab13d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0438 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0439, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0438 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0439, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0440, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0441, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0442, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0443)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0438 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0439, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0440, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0441, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0442, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0443)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0438 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0439, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0440, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0441, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0442, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0443) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0438 (+5 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0439, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0440, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0441, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0442, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0443).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0095__2

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0438 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_438 (a z s c : ℝ)
    (ha : Bounds (969 / 5000) (1939 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (968031 / 10000000) (1940939 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (95593127518600498616895493 / 231573439103808400000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1939 / 10000)
  have hx1 : Bounds (11939 / 10000) (11939 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1939 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1939 / 10000)
  have hx2 : Bounds (11939 / 10000) (11939 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1939 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (177225259 / 1000000000) (8861263 / 50000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6102.1) (by simpa only [div_one] using reflection_log_6102.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (2644865459 / 12500000000) (105794618957 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1939 / 10000)
  have hx5 : Bounds (-1939 / 10000) (-1939 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1939 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8061 / 10000) (8061 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1939 / 10000)
  have hx7 : Bounds (8061 / 10000) (8061 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1939 / 10000)
  have hx8 : Bounds (-1939 / 10000) (-1939 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1939 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8061 / 10000) (8061 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1939 / 10000)
  have hx10 : Bounds (8061 / 10000) (8061 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-8621899 / 40000000) (-107773737 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_6103.1) (by simpa only [div_one] using reflection_log_6103.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-86876409799 / 500000000000) (-173752818791 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (18918208561 / 500000000000) (37836419123 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (18918208561 / 1000000000000) (9459104781 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (18918208561 / 1000000000000) (9459104781 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-9459104781 / 500000000000) (-18918208561 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (337114485219 / 500000000000) (674228972439 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (337114485219 / 500000000000) (674228972439 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1939 / 10000)
  have hx20 : Bounds (337114485219 / 500000000000) (674228972439 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(969 / 5000)
  have hx22 : Bounds (5969 / 5000) (5969 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((969 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(969 / 5000)
  have hx23 : Bounds (5969 / 5000) (5969 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((969 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (22142687 / 125000000) (177141497 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6088.1) (by simpa only [div_one] using reflection_log_6088.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (52867879481 / 250000000000) (211471519119 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(969 / 5000)
  have hx26 : Bounds (-969 / 5000) (-969 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((969 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4031 / 5000) (4031 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(969 / 5000)
  have hx28 : Bounds (4031 / 5000) (4031 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(969 / 5000)
  have hx29 : Bounds (-969 / 5000) (-969 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((969 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4031 / 5000) (4031 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(969 / 5000)
  have hx31 : Bounds (4031 / 5000) (4031 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-215423429 / 1000000000) (-53855857 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_6089.1) (by simpa only [div_one] using reflection_log_6089.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-8683718423 / 50000000000) (-173674367653 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (4724643683 / 125000000000) (18898575733 / 500000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (4724643683 / 250000000000) (18898575733 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (4724643683 / 250000000000) (18898575733 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18898575733 / 1000000000000) (-4724643683 / 250000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (674248604267 / 1000000000000) (168562151567 / 250000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (674248604267 / 1000000000000) (168562151567 / 250000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (969 / 5000)
  have hx41 : Bounds (674248604267 / 1000000000000) (168562151567 / 250000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (337114485219 / 500000000000) (168562151567 / 250000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1939 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1939 / 10000000)
  have hx45 : Bounds (10001939 / 10000000) (10001939 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1939 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1939 / 10000000)
  have hx46 : Bounds (10001939 / 10000000) (10001939 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1939 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (193881 / 1000000000) (96941 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_6104.1) (by simpa only [div_one] using reflection_log_6104.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (193918593 / 1000000000000) (96959797 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1939 / 10000000)
  have hx49 : Bounds (-1939 / 10000000) (-1939 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1939 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998061 / 10000000) (9998061 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1939 / 10000000)
  have hx51 : Bounds (9998061 / 10000000) (9998061 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1939 / 10000000)
  have hx52 : Bounds (-1939 / 10000000) (-1939 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1939 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998061 / 10000000) (9998061 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1939 / 10000000)
  have hx54 : Bounds (9998061 / 10000000) (9998061 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-193919 / 1000000000) (-96959 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6105.1) (by simpa only [div_one] using reflection_log_6105.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-969407 / 5000000000) (-193880399 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (37193 / 1000000000000) (7839 / 200000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (4649 / 250000000000) (9799 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (4649 / 250000000000) (9799 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-9799 / 500000000000) (-4649 / 250000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346573580201 / 500000000000) (173286790601 / 250000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346573580201 / 500000000000) (173286790601 / 250000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1939 / 10000000)
  have hx64 : Bounds (346573580201 / 500000000000) (173286790601 / 250000000000) x64 := by
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
  have hx86 : Bounds (346573580201 / 500000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (34184403271 / 25000000000) (341848946817 / 250000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (34184403271 / 50000000000) (341848946817 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (34184403271 / 50000000000) (341848946817 / 500000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (5152145430639 / 500000000000) (10330247688349 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (880615085559 / 125000000000) (3531384292621 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (880615085559 / 125000000000) (3531384292621 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(97467 / 1000000)
  have hx95 : Bounds (1097467 / 1000000) (1097467 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97467 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(97467 / 1000000)
  have hx96 : Bounds (1097467 / 1000000) (1097467 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97467 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (93004797 / 1000000000) (46502399 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_6106.1) (by simpa only [div_one] using reflection_log_6106.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (102069695549 / 1000000000000) (102069696647 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(97467 / 1000000)
  have hx99 : Bounds (-97467 / 1000000) (-97467 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97467 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (902533 / 1000000) (902533 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(97467 / 1000000)
  have hx101 : Bounds (902533 / 1000000) (902533 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(97467 / 1000000)
  have hx102 : Bounds (-97467 / 1000000) (-97467 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97467 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (902533 / 1000000) (902533 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(97467 / 1000000)
  have hx104 : Bounds (902533 / 1000000) (902533 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-4102001 / 40000000) (-12818753 / 125000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_6107.1) (by simpa only [div_one] using reflection_log_6107.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-46277390857 / 500000000000) (-9255478081 / 100000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (1902982767 / 200000000000) (9514915837 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4757456917 / 1000000000000) (4757457919 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4757456917 / 1000000000000) (4757457919 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4757457919 / 1000000000000) (-4757456917 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688389722081 / 1000000000000) (688389724083 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688389722081 / 1000000000000) (688389724083 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (97467 / 1000000)
  have hx114 : Bounds (688389722081 / 1000000000000) (688389724083 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(97711 / 1000000)
  have hx116 : Bounds (1097711 / 1000000) (1097711 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97711 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(97711 / 1000000)
  have hx117 : Bounds (1097711 / 1000000) (1097711 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97711 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (46613551 / 500000000) (93227103 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_6108.1) (by simpa only [div_one] using reflection_log_6108.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (102336415363 / 1000000000000) (51168208231 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(97711 / 1000000)
  have hx120 : Bounds (-97711 / 1000000) (-97711 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97711 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (902289 / 1000000) (902289 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(97711 / 1000000)
  have hx122 : Bounds (902289 / 1000000) (902289 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(97711 / 1000000)
  have hx123 : Bounds (-97711 / 1000000) (-97711 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97711 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (902289 / 1000000) (902289 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(97711 / 1000000)
  have hx125 : Bounds (902289 / 1000000) (902289 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-25705103 / 250000000) (-102820411 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_6109.1) (by simpa only [div_one] using reflection_log_6109.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-23193431681 / 250000000000) (-4638686291 / 50000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (9562688639 / 1000000000000) (4781345321 / 500000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4781344319 / 1000000000000) (4781345321 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4781344319 / 1000000000000) (4781345321 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4781345321 / 1000000000000) (-4781344319 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (688365834679 / 1000000000000) (688365836681 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (688365834679 / 1000000000000) (688365836681 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (97711 / 1000000)
  have hx135 : Bounds (688365834679 / 1000000000000) (688365836681 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(97467 / 1000000)
  have hx136 : Bounds (686647284353 / 1000000000000) (344193432849 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((97467 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(97711 / 1000000)
  have hx137 : Bounds (137673249 / 200000000) (690110181233 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((97711 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (97467 / 1000000) (97711 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(97467 / 1000000) ≤ (344193432849 / 500000000000) := hx136.2
      have h2 : (688389722081 / 1000000000000) ≤ biasE (97467 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (97711 / 1000000) ≤ (688365836681 / 1000000000000) := hx135.2
      have h2 : (137673249 / 200000000) ≤ x93*(97711 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(97711 / 1000000)
  have hx139 : Bounds (1097711 / 1000000) (1097711 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97711 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(97711 / 1000000)
  have hx140 : Bounds (1097711 / 1000000) (1097711 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97711 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (46613551 / 500000000) (93227103 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_6108.1) (by simpa only [div_one] using reflection_log_6108.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (102336415363 / 1000000000000) (51168208231 / 500000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(97711 / 1000000)
  have hx143 : Bounds (-97711 / 1000000) (-97711 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97711 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (902289 / 1000000) (902289 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(97711 / 1000000)
  have hx145 : Bounds (902289 / 1000000) (902289 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(97711 / 1000000)
  have hx146 : Bounds (-97711 / 1000000) (-97711 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97711 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (902289 / 1000000) (902289 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(97711 / 1000000)
  have hx148 : Bounds (902289 / 1000000) (902289 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-25705103 / 250000000) (-102820411 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_6109.1) (by simpa only [div_one] using reflection_log_6109.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-23193431681 / 250000000000) (-4638686291 / 50000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (9562688639 / 1000000000000) (4781345321 / 500000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4781344319 / 1000000000000) (4781345321 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4781344319 / 1000000000000) (4781345321 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4781345321 / 1000000000000) (-4781344319 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (688365834679 / 1000000000000) (688365836681 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (688365834679 / 1000000000000) (688365836681 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (97711 / 1000000)
  have hx158 : Bounds (688365834679 / 1000000000000) (688365836681 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(97467 / 1000000)
  have hx160 : Bounds (1097467 / 1000000) (1097467 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97467 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(97467 / 1000000)
  have hx161 : Bounds (1097467 / 1000000) (1097467 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97467 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (93004797 / 1000000000) (46502399 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_6106.1) (by simpa only [div_one] using reflection_log_6106.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (102069695549 / 1000000000000) (102069696647 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(97467 / 1000000)
  have hx164 : Bounds (-97467 / 1000000) (-97467 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97467 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (902533 / 1000000) (902533 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(97467 / 1000000)
  have hx166 : Bounds (902533 / 1000000) (902533 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(97467 / 1000000)
  have hx167 : Bounds (-97467 / 1000000) (-97467 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97467 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (902533 / 1000000) (902533 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(97467 / 1000000)
  have hx169 : Bounds (902533 / 1000000) (902533 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-4102001 / 40000000) (-12818753 / 125000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_6107.1) (by simpa only [div_one] using reflection_log_6107.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-46277390857 / 500000000000) (-9255478081 / 100000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (1902982767 / 200000000000) (9514915837 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4757456917 / 1000000000000) (4757457919 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4757456917 / 1000000000000) (4757457919 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4757457919 / 1000000000000) (-4757456917 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688389722081 / 1000000000000) (688389724083 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688389722081 / 1000000000000) (688389724083 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (97467 / 1000000)
  have hx179 : Bounds (688389722081 / 1000000000000) (688389724083 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (688365834679 / 1000000000000) (688389724083 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-9547439521 / 1000000000000) (-9499816089 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-9593309 / 1000000000) (-9545227 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_6110.1) (by simpa only [div_one] using reflection_log_6111.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-9593309 / 2000000000) (-9545227 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-9593309 / 2000000000) (-9545227 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (9545227 / 2000000000) (9593309 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1395839587 / 2000000000) (1395887671 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1395839587 / 2000000000) (1395887671 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (97467 / 1000000) (97711 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-9547439521 / 1000000000000) (-9499816089 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1097467 / 1000000) (1097711 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-97711 / 1000000) (-97467 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (902289 / 1000000) (902533 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (902289 / 1000000) (902533 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (221598545427 / 200000000000) (69268272139 / 62500000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (121598545427 / 100000000000) (38018272139 / 31250000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (121598545427 / 100000000000) (38018272139 / 31250000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (195554821 / 1000000000) (98023757 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_6112.1) (by simpa only [div_one] using reflection_log_6113.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (195554821 / 2000000000) (98023757 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (195554821 / 2000000000) (98023757 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (5969 / 5000) (11939 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1939 / 10000) (-969 / 5000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8061 / 10000) (4031 / 5000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8061 / 10000) (4031 / 5000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (155048375093 / 125000000000) (620270437911 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (92548375093 / 62500000000) (370270437911 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (92548375093 / 62500000000) (370270437911 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (15702597 / 40000000) (78554547 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_6114.1) (by simpa only [div_one] using reflection_log_6115.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (15702597 / 80000000) (78554547 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (15702597 / 80000000) (78554547 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1395839587 / 1000000000) (1395887671 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (97467 / 1000000) (97711 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-9547439521 / 1000000000000) (-9499816089 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386292147479 / 1000000000000) (1386387854911 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386292147479 / 1000000000000) (1386387854911 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (119284518901 / 125000000000) (190875030583 / 200000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (34184403271 / 25000000000) (341848946817 / 250000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (980996274559 / 1000000000000) (122636326791 / 125000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (980996274559 / 1000000000000) (122636326791 / 125000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (670695445137 / 500000000000) (1341539172961 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1395839587 / 2000000000) (1395887671 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (487092038159 / 1000000000000) (487125597513 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339951174687 / 1000000000000) (339986307899 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339951174687 / 1000000000000) (339986307899 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456007408863 / 1000000000000) (456104950317 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1096238924073 / 500000000000) (2192946826223 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2092229322537 / 1000000000000) (523223490653 / 250000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2092229322537 / 1000000000000) (523223490653 / 250000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-98023757 / 1000000000) (-195554821 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1395839587 / 1000000000) (1395887671 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (97467 / 1000000) (97711 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-9547439521 / 1000000000000) (-9499816089 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386292147479 / 1000000000000) (1386387854911 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386292147479 / 1000000000000) (1386387854911 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-67949473099 / 500000000000) (-16943507047 / 125000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (504795464071 / 500000000000) (201927894359 / 200000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (98401798993 / 1000000000000) (98652882429 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (98401798993 / 1000000000000) (98652882429 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (98401798993 / 500000000000) (98652882429 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (97467 / 500000) (97711 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-97711 / 500000) (-97467 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (690798993 / 500000000000) (1185882429 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (690798993 / 500000000000) (1185882429 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (19020897 / 20000000000) (1632698557 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-33736975337 / 250000000000) (-133915357819 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (34184403271 / 25000000000) (341848946817 / 250000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (980996274559 / 1000000000000) (122636326791 / 125000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (980996274559 / 1000000000000) (122636326791 / 125000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (670695445137 / 500000000000) (1341539172961 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1395839587 / 2000000000) (1395887671 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (487092038159 / 1000000000000) (487125597513 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339951174687 / 1000000000000) (339986307899 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339951174687 / 1000000000000) (339986307899 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456007408863 / 1000000000000) (456104950317 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1096238924073 / 500000000000) (2192946826223 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-295933571967 / 1000000000000) (-36700806943 / 125000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-295933571967 / 1000000000000) (-36700806943 / 125000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (97467 / 250000) (97711 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (504795464071 / 500000000000) (201927894359 / 200000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (98401798993 / 250000000000) (78922305943 / 200000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (98401798993 / 250000000000) (78922305943 / 200000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (292401 / 1000000) (293133 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691256446481 / 1000000000000) (691313497423 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1446521735403 / 1000000000000) (1446641120081 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (422964401953 / 1000000000000) (424058251453 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (422964401953 / 1000000000000) (424058251453 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-424058251453 / 1000000000000) (-422964401953 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-30451055481 / 1000000000000) (-14176436119 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-30451055481 / 1000000000000) (-14176436119 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-15932707543 / 250000000000) (-29660355337 / 500000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-359664402139 / 1000000000000) (-176463583109 / 500000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1395839587 / 1000000000) (1395887671 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (97467 / 1000000) (97711 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (9499816089 / 1000000000000) (9547439521 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-9547439521 / 1000000000000) (-9499816089 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386292147479 / 1000000000000) (1386387854911 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386292147479 / 1000000000000) (1386387854911 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (67558868369 / 500000000000) (33866335923 / 250000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (990452560479 / 1000000000000) (990500183911 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (980996274559 / 1000000000000) (122636326791 / 125000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (980996274559 / 1000000000000) (122636326791 / 125000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1395839587 / 2000000000) (1395887671 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (487092038159 / 1000000000000) (487125597513 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (487092038159 / 1000000000000) (487125597513 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (477835474801 / 1000000000000) (477914351719 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (1046212565497 / 500000000000) (209277053031 / 100000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (282723747993 / 1000000000000) (283497879157 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (282723747993 / 1000000000000) (283497879157 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (4782765693 / 250000000000) (3837821671 / 200000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (707496897451 / 1000000000000) (353789416219 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (707496897451 / 1000000000000) (353789416219 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (250275929951 / 500000000000) (100133560823 / 200000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (250275929951 / 500000000000) (100133560823 / 200000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-90036193219 / 500000000000) (-8832917473 / 50000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2092229322537 / 500000000000) (523223490653 / 125000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (4782765693 / 250000000000) (3837821671 / 200000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (707496897451 / 1000000000000) (353789416219 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2960491508901 / 1000000000000) (740443733241 / 250000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-98023757 / 1000000000) (-195554821 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (196517411 / 2000000000) (98608957 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (196517411 / 2000000000) (98608957 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (72723515827 / 250000000000) (292057537009 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (11082167687 / 100000000000) (115399187549 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (969 / 5000) (1939 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (938961 / 25000000) (3759721 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (938961 / 25000000) (3759721 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3759721 / 100000000) (-938961 / 25000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96240279 / 100000000) (24061039 / 25000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96240279 / 100000000) (24061039 / 25000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1039024125267 / 1000000000000) (1039065981927 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1039024125267 / 1000000000000) (1039065981927 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1039024125267 / 1000000000000) (1039065981927 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (5875135899 / 20000000000) (294573002181 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (20228923591 / 50000000000) (40997218973 / 100000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (688365834679 / 1000000000000) (688389724083 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (473847522353 / 1000000000000) (7404381441 / 15625000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (473847522353 / 1000000000000) (7404381441 / 15625000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (191708506469 / 1000000000000) (19427779027 / 100000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (119289858359 / 250000000000) (477182730207 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2095633258911 / 1000000000000) (1047867787921 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (100437680543 / 250000000000) (81430975333 / 200000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (100437680543 / 250000000000) (81430975333 / 200000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (95593127518600498616895493 / 231573439103808400000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_438 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((969 / 5000):ℝ) ((1939 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (95593127518600498616895493 / 231573439103808400000000000) := by
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
  have hsl : (968031 / 10000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1940939 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1939 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_438 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_438 {a z : ℝ}
    (ha : a ∈ Set.Icc ((969 / 5000):ℝ) ((1939 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_438 ha ⟨hz.1.le,hz.2⟩ hs) (M := (95593127518600498616895493 / 231573439103808400000000000))
  exact lt_of_lt_of_le (by norm_num : (95593127518600498616895493 / 231573439103808400000000000) < 2*((969 / 5000):ℝ)/(1-((969 / 5000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0439 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_439 (a z s c : ℝ)
    (ha : Bounds (1939 / 10000) (97 / 500) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1937061 / 20000000) (97097 / 1000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (3825668521686460964962154017 / 9262191301997841000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(97 / 500)
  have hx1 : Bounds (597 / 500) (597 / 500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(97 / 500)
  have hx2 : Bounds (597 / 500) (597 / 500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (88654507 / 500000000) (35461803 / 200000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6116.1) (by simpa only [div_one] using reflection_log_6116.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (52926740679 / 250000000000) (21170696391 / 100000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(97 / 500)
  have hx5 : Bounds (-97 / 500) (-97 / 500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (403 / 500) (403 / 500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(97 / 500)
  have hx7 : Bounds (403 / 500) (403 / 500) x7 := by
    exact hx6
  let x8 : ℝ := -(97 / 500)
  have hx8 : Bounds (-97 / 500) (-97 / 500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (403 / 500) (403 / 500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(97 / 500)
  have hx10 : Bounds (403 / 500) (403 / 500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-215671537 / 1000000000) (-13479471 / 62500000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_6117.1) (by simpa only [div_one] using reflection_log_6117.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-86915629411 / 500000000000) (-5432226813 / 31250000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (18937851947 / 500000000000) (18937852947 / 500000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (18937851947 / 1000000000000) (18937852947 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (18937851947 / 1000000000000) (18937852947 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18937852947 / 1000000000000) (-18937851947 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674209327053 / 1000000000000) (674209329053 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674209327053 / 1000000000000) (674209329053 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (97 / 500)
  have hx20 : Bounds (674209327053 / 1000000000000) (674209329053 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1939 / 10000)
  have hx22 : Bounds (11939 / 10000) (11939 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1939 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1939 / 10000)
  have hx23 : Bounds (11939 / 10000) (11939 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1939 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (177225259 / 1000000000) (8861263 / 50000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6102.1) (by simpa only [div_one] using reflection_log_6102.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (2644865459 / 12500000000) (105794618957 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1939 / 10000)
  have hx26 : Bounds (-1939 / 10000) (-1939 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1939 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8061 / 10000) (8061 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1939 / 10000)
  have hx28 : Bounds (8061 / 10000) (8061 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1939 / 10000)
  have hx29 : Bounds (-1939 / 10000) (-1939 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1939 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8061 / 10000) (8061 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1939 / 10000)
  have hx31 : Bounds (8061 / 10000) (8061 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-8621899 / 40000000) (-107773737 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_6103.1) (by simpa only [div_one] using reflection_log_6103.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-86876409799 / 500000000000) (-173752818791 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (18918208561 / 500000000000) (37836419123 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (18918208561 / 1000000000000) (9459104781 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (18918208561 / 1000000000000) (9459104781 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-9459104781 / 500000000000) (-18918208561 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (337114485219 / 500000000000) (674228972439 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (337114485219 / 500000000000) (674228972439 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1939 / 10000)
  have hx41 : Bounds (337114485219 / 500000000000) (674228972439 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674209327053 / 1000000000000) (674228972439 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (97 / 500000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(97 / 500000)
  have hx45 : Bounds (500097 / 500000) (500097 / 500000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 500000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(97 / 500000)
  have hx46 : Bounds (500097 / 500000) (500097 / 500000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 500000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (193981 / 1000000000) (96991 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_6118.1) (by simpa only [div_one] using reflection_log_6118.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (24252329 / 125000000000) (194019633 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(97 / 500000)
  have hx49 : Bounds (-97 / 500000) (-97 / 500000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 500000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (499903 / 500000) (499903 / 500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(97 / 500000)
  have hx51 : Bounds (499903 / 500000) (499903 / 500000) x51 := by
    exact hx50
  let x52 : ℝ := -(97 / 500000)
  have hx52 : Bounds (-97 / 500000) (-97 / 500000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 500000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (499903 / 500000) (499903 / 500000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(97 / 500000)
  have hx54 : Bounds (499903 / 500000) (499903 / 500000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-194019 / 1000000000) (-97009 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6119.1) (by simpa only [div_one] using reflection_log_6119.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-193981361 / 1000000000000) (-4849509 / 25000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (37271 / 1000000000000) (39273 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (3727 / 200000000000) (19637 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (3727 / 200000000000) (19637 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-19637 / 1000000000000) (-3727 / 200000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147160363 / 1000000000000) (138629432473 / 200000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147160363 / 1000000000000) (138629432473 / 200000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (97 / 500000)
  have hx64 : Bounds (693147160363 / 1000000000000) (138629432473 / 200000000000) x64 := by
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
  have hx86 : Bounds (693147160363 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (170919560927 / 125000000000) (1367376153439 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (170919560927 / 250000000000) (8546100959 / 12500000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (170919560927 / 250000000000) (8546100959 / 12500000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (1287372421393 / 125000000000) (10324920072213 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (110018564507 / 15625000000) (352951237323 / 50000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (110018564507 / 15625000000) (352951237323 / 50000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(48759 / 500000)
  have hx95 : Bounds (548759 / 500000) (548759 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48759 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(48759 / 500000)
  have hx96 : Bounds (548759 / 500000) (548759 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48759 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (46525633 / 500000000) (93051267 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_6120.1) (by simpa only [div_one] using reflection_log_6120.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (102125439357 / 1000000000000) (12765680057 / 125000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(48759 / 500000)
  have hx99 : Bounds (-48759 / 500000) (-48759 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48759 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (451241 / 500000) (451241 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(48759 / 500000)
  have hx101 : Bounds (451241 / 500000) (451241 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(48759 / 500000)
  have hx102 : Bounds (-48759 / 500000) (-48759 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48759 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (451241 / 500000) (451241 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(48759 / 500000)
  have hx104 : Bounds (451241 / 500000) (451241 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-51303267 / 500000000) (-102606533 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_6121.1) (by simpa only [div_one] using reflection_log_6121.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-46300275009 / 500000000000) (-46300274557 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (9524889339 / 1000000000000) (4762445671 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4762444669 / 1000000000000) (4762445671 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4762444669 / 1000000000000) (4762445671 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4762445671 / 1000000000000) (-4762444669 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688384734329 / 1000000000000) (688384736331 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688384734329 / 1000000000000) (688384736331 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (48759 / 500000)
  have hx114 : Bounds (688384734329 / 1000000000000) (688384736331 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(97763 / 1000000)
  have hx116 : Bounds (1097763 / 1000000) (1097763 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97763 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(97763 / 1000000)
  have hx117 : Bounds (1097763 / 1000000) (1097763 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97763 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (11659309 / 125000000) (93274473 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_6122.1) (by simpa only [div_one] using reflection_log_6122.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (51196632103 / 500000000000) (12799158163 / 125000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(97763 / 1000000)
  have hx120 : Bounds (-97763 / 1000000) (-97763 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97763 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (902237 / 1000000) (902237 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(97763 / 1000000)
  have hx122 : Bounds (902237 / 1000000) (902237 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(97763 / 1000000)
  have hx123 : Bounds (-97763 / 1000000) (-97763 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97763 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (902237 / 1000000) (902237 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(97763 / 1000000)
  have hx125 : Bounds (902237 / 1000000) (902237 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-25719511 / 250000000) (-102878043 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_6123.1) (by simpa only [div_one] using reflection_log_6123.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-18564075557 / 200000000000) (-46410188441 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (9572886421 / 1000000000000) (4786444211 / 500000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (478644321 / 100000000000) (4786444211 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (478644321 / 100000000000) (4786444211 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4786444211 / 1000000000000) (-478644321 / 100000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (688360735789 / 1000000000000) (68836073779 / 100000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (688360735789 / 1000000000000) (68836073779 / 100000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (97763 / 1000000)
  have hx135 : Bounds (688360735789 / 1000000000000) (68836073779 / 100000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(48759 / 500000)
  have hx136 : Bounds (686642583909 / 1000000000000) (344190987613 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((48759 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(97763 / 1000000)
  have hx137 : Bounds (688367675001 / 1000000000000) (690111436289 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((97763 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (48759 / 500000) (97763 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(48759 / 500000) ≤ (344190987613 / 500000000000) := hx136.2
      have h2 : (688384734329 / 1000000000000) ≤ biasE (48759 / 500000) := hx114.1
      linarith
    · have h1 : biasE (97763 / 1000000) ≤ (68836073779 / 100000000000) := hx135.2
      have h2 : (688367675001 / 1000000000000) ≤ x93*(97763 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(97763 / 1000000)
  have hx139 : Bounds (1097763 / 1000000) (1097763 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97763 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(97763 / 1000000)
  have hx140 : Bounds (1097763 / 1000000) (1097763 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97763 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (11659309 / 125000000) (93274473 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_6122.1) (by simpa only [div_one] using reflection_log_6122.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (51196632103 / 500000000000) (12799158163 / 125000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(97763 / 1000000)
  have hx143 : Bounds (-97763 / 1000000) (-97763 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97763 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (902237 / 1000000) (902237 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(97763 / 1000000)
  have hx145 : Bounds (902237 / 1000000) (902237 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(97763 / 1000000)
  have hx146 : Bounds (-97763 / 1000000) (-97763 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97763 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (902237 / 1000000) (902237 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(97763 / 1000000)
  have hx148 : Bounds (902237 / 1000000) (902237 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-25719511 / 250000000) (-102878043 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_6123.1) (by simpa only [div_one] using reflection_log_6123.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-18564075557 / 200000000000) (-46410188441 / 500000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (9572886421 / 1000000000000) (4786444211 / 500000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (478644321 / 100000000000) (4786444211 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (478644321 / 100000000000) (4786444211 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4786444211 / 1000000000000) (-478644321 / 100000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (688360735789 / 1000000000000) (68836073779 / 100000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (688360735789 / 1000000000000) (68836073779 / 100000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (97763 / 1000000)
  have hx158 : Bounds (688360735789 / 1000000000000) (68836073779 / 100000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(48759 / 500000)
  have hx160 : Bounds (548759 / 500000) (548759 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48759 / 500000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(48759 / 500000)
  have hx161 : Bounds (548759 / 500000) (548759 / 500000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48759 / 500000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (46525633 / 500000000) (93051267 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_6120.1) (by simpa only [div_one] using reflection_log_6120.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (102125439357 / 1000000000000) (12765680057 / 125000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(48759 / 500000)
  have hx164 : Bounds (-48759 / 500000) (-48759 / 500000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48759 / 500000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (451241 / 500000) (451241 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(48759 / 500000)
  have hx166 : Bounds (451241 / 500000) (451241 / 500000) x166 := by
    exact hx165
  let x167 : ℝ := -(48759 / 500000)
  have hx167 : Bounds (-48759 / 500000) (-48759 / 500000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48759 / 500000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (451241 / 500000) (451241 / 500000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(48759 / 500000)
  have hx169 : Bounds (451241 / 500000) (451241 / 500000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-51303267 / 500000000) (-102606533 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_6121.1) (by simpa only [div_one] using reflection_log_6121.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-46300275009 / 500000000000) (-46300274557 / 500000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (9524889339 / 1000000000000) (4762445671 / 500000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4762444669 / 1000000000000) (4762445671 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4762444669 / 1000000000000) (4762445671 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4762445671 / 1000000000000) (-4762444669 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688384734329 / 1000000000000) (688384736331 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688384734329 / 1000000000000) (688384736331 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (48759 / 500000)
  have hx179 : Bounds (688384734329 / 1000000000000) (688384736331 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (688360735789 / 1000000000000) (688384736331 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-9557604169 / 1000000000000) (-2377440081 / 250000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-2400893 / 250000000) (-4777633 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_6124.1) (by simpa only [div_one] using reflection_log_6125.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-2400893 / 500000000) (-4777633 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-2400893 / 500000000) (-4777633 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (4777633 / 1000000000) (2400893 / 500000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (697924813 / 1000000000) (697948967 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (697924813 / 1000000000) (697948967 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (48759 / 500000) (97763 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-9557604169 / 1000000000000) (-2377440081 / 250000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (548759 / 500000) (1097763 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-97763 / 1000000) (-48759 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (902237 / 1000000) (451241 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (902237 / 1000000) (451241 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (221611068143 / 200000000000) (554178115063 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (121611068143 / 100000000000) (304178115063 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (121611068143 / 100000000000) (304178115063 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (978289 / 5000000) (196152517 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_6126.1) (by simpa only [div_one] using reflection_log_6127.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (978289 / 10000000) (196152517 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (978289 / 10000000) (196152517 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11939 / 10000) (597 / 500) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-97 / 500) (-1939 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (403 / 500) (8061 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (403 / 500) (8061 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1240540875821 / 1000000000000) (620347394541 / 500000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (740540875821 / 500000000000) (370347394541 / 250000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (740540875821 / 500000000000) (370347394541 / 250000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (196386367 / 500000000) (49122569 / 125000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_6128.1) (by simpa only [div_one] using reflection_log_6129.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (196386367 / 1000000000) (49122569 / 250000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (196386367 / 1000000000) (49122569 / 250000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (697924813 / 500000000) (697948967 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (48759 / 500000) (97763 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-9557604169 / 1000000000000) (-2377440081 / 250000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386292021831 / 1000000000000) (346597043419 / 250000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386292021831 / 1000000000000) (346597043419 / 250000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477134498083 / 500000000000) (954368457389 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (170919560927 / 125000000000) (8546100959 / 6250000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (980976139459 / 1000000000000) (490535457447 / 500000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (980976139459 / 1000000000000) (490535457447 / 500000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1341344088289 / 1000000000000) (67074648693 / 50000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (697924813 / 1000000000) (697948967 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (487099044601 / 1000000000000) (487132760537 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (67991701923 / 200000000000) (339993807009 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (67991701923 / 200000000000) (339993807009 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (91200267427 / 200000000000) (456099303259 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2192504993659 / 1000000000000) (2192976025647 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2092239539387 / 1000000000000) (32701674167 / 15625000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2092239539387 / 1000000000000) (32701674167 / 15625000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-196152517 / 2000000000) (-978289 / 10000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (697924813 / 500000000) (697948967 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (48759 / 500000) (97763 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-9557604169 / 1000000000000) (-2377440081 / 250000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386292021831 / 1000000000000) (346597043419 / 250000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386292021831 / 1000000000000) (346597043419 / 250000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-135971764903 / 1000000000000) (-67809711787 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (504800532071 / 500000000000) (504824916729 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (24613569143 / 250000000000) (98706396669 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (24613569143 / 250000000000) (98706396669 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (24613569143 / 125000000000) (98706396669 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (48759 / 250000) (97763 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-97763 / 500000) (-48759 / 250000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (172819143 / 125000000000) (1188396669 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (172819143 / 125000000000) (1188396669 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (951695299 / 1000000000000) (51129633 / 31250000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-33755017401 / 250000000000) (-66991637659 / 500000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (170919560927 / 125000000000) (8546100959 / 6250000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (980976139459 / 1000000000000) (490535457447 / 500000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (980976139459 / 1000000000000) (490535457447 / 500000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1341344088289 / 1000000000000) (67074648693 / 50000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (697924813 / 1000000000) (697948967 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (487099044601 / 1000000000000) (487132760537 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (67991701923 / 200000000000) (339993807009 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (67991701923 / 200000000000) (339993807009 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (91200267427 / 200000000000) (456099303259 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2192504993659 / 1000000000000) (2192976025647 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-296095775623 / 1000000000000) (-293759000201 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-296095775623 / 1000000000000) (-293759000201 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (48759 / 125000) (97763 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (504800532071 / 500000000000) (504824916729 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (393817106291 / 1000000000000) (197412793337 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (393817106291 / 1000000000000) (197412793337 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (146277 / 500000) (293289 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691254323897 / 1000000000000) (345655819803 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (361631405689 / 250000000000) (22603836909 / 15625000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (423186857039 / 1000000000000) (212142615143 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (423186857039 / 1000000000000) (212142615143 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-212142615143 / 500000000000) (-423186857039 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-6093624799 / 200000000000) (-5672254073 / 200000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-6093624799 / 200000000000) (-5672254073 / 200000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-7970869307 / 125000000000) (-14834642811 / 250000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-359862730079 / 1000000000000) (-70619514289 / 200000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (697924813 / 500000000) (697948967 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (48759 / 500000) (97763 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (2377440081 / 250000000000) (9557604169 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-9557604169 / 1000000000000) (-2377440081 / 250000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386292021831 / 1000000000000) (346597043419 / 250000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386292021831 / 1000000000000) (346597043419 / 250000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (16898553173 / 125000000000) (8471091689 / 62500000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (990442395831 / 1000000000000) (247622559919 / 250000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (980976139459 / 1000000000000) (490535457447 / 500000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (980976139459 / 1000000000000) (490535457447 / 500000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (697924813 / 1000000000) (697948967 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (487099044601 / 1000000000000) (487132760537 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (487099044601 / 1000000000000) (487132760537 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (238916270153 / 500000000000) (95582356611 / 200000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (209243637729 / 100000000000) (2092783382563 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (141436589531 / 500000000000) (283650558703 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (141436589531 / 500000000000) (283650558703 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (19151205737 / 1000000000000) (19209478853 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (353755970763 / 500000000000) (44224638449 / 62500000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (353755970763 / 500000000000) (44224638449 / 62500000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (500573147401 / 1000000000000) (250344786681 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (500573147401 / 1000000000000) (250344786681 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-180179516793 / 1000000000000) (-176751162677 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2092239539387 / 500000000000) (32701674167 / 7812500000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (19151205737 / 1000000000000) (19209478853 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (353755970763 / 500000000000) (44224638449 / 62500000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1480284458649 / 500000000000) (740464494957 / 250000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-196152517 / 2000000000) (-978289 / 10000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (196620217 / 2000000000) (192698 / 1953125) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (196620217 / 2000000000) (192698 / 1953125) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (291053851481 / 1000000000000) (292220983807 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (3464822959 / 31250000000) (11546982113 / 100000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1939 / 10000) (97 / 500) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3759721 / 100000000) (9409 / 250000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3759721 / 100000000) (9409 / 250000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-9409 / 250000) (-3759721 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (240591 / 250000) (96240279 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (240591 / 250000) (96240279 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (519532990963 / 500000000000) (1039107863553 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (519532990963 / 500000000000) (1039107863553 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (519532990963 / 500000000000) (1039107863553 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (146961948781 / 500000000000) (5894870521 / 20000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (1619192929 / 4000000000) (20510667359 / 50000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (688360735789 / 1000000000000) (688384736331 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (18953620103 / 40000000000) (236936772607 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (18953620103 / 40000000000) (236936772607 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (19180979781 / 100000000000) (194389253123 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (59644501299 / 125000000000) (477179386897 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2095647941757 / 1000000000000) (2095750610327 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (401965807989 / 1000000000000) (203695697937 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (401965807989 / 1000000000000) (203695697937 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (3825668521686460964962154017 / 9262191301997841000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_439 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1939 / 10000):ℝ) ((97 / 500)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (3825668521686460964962154017 / 9262191301997841000000000000) := by
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
  have hsl : (1937061 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (97097 / 1000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (97 / 500))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_439 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_439 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1939 / 10000):ℝ) ((97 / 500)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_439 ha ⟨hz.1.le,hz.2⟩ hs) (M := (3825668521686460964962154017 / 9262191301997841000000000000))
  exact lt_of_lt_of_le (by norm_num : (3825668521686460964962154017 / 9262191301997841000000000000) < 2*((1939 / 10000):ℝ)/(1-((1939 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0440 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_440 (a z s c : ℝ)
    (ha : Bounds (97 / 500) (1941 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (96903 / 1000000) (1942941 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (11961150547486215148201 / 28942014640500000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1941 / 10000)
  have hx1 : Bounds (11941 / 10000) (11941 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1941 / 10000)
  have hx2 : Bounds (11941 / 10000) (11941 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (177392763 / 1000000000) (44348191 / 250000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6130.1) (by simpa only [div_one] using reflection_log_6130.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (105912349149 / 500000000000) (211824699493 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1941 / 10000)
  have hx5 : Bounds (-1941 / 10000) (-1941 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8059 / 10000) (8059 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1941 / 10000)
  have hx7 : Bounds (8059 / 10000) (8059 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1941 / 10000)
  have hx8 : Bounds (-1941 / 10000) (-1941 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8059 / 10000) (8059 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1941 / 10000)
  have hx10 : Bounds (8059 / 10000) (8059 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-107897807 / 500000000) (-215795613 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_6131.1) (by simpa only [div_one] using reflection_log_6131.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-173909685323 / 1000000000000) (-43477421129 / 250000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (1516600519 / 40000000000) (37915014977 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (18957506487 / 1000000000000) (18957507489 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (18957506487 / 1000000000000) (18957507489 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18957507489 / 1000000000000) (-18957506487 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674189672511 / 1000000000000) (674189674513 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674189672511 / 1000000000000) (674189674513 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1941 / 10000)
  have hx20 : Bounds (674189672511 / 1000000000000) (674189674513 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(97 / 500)
  have hx22 : Bounds (597 / 500) (597 / 500) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 500) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(97 / 500)
  have hx23 : Bounds (597 / 500) (597 / 500) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 500) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (88654507 / 500000000) (35461803 / 200000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6116.1) (by simpa only [div_one] using reflection_log_6116.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (52926740679 / 250000000000) (21170696391 / 100000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(97 / 500)
  have hx26 : Bounds (-97 / 500) (-97 / 500) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 500) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (403 / 500) (403 / 500) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(97 / 500)
  have hx28 : Bounds (403 / 500) (403 / 500) x28 := by
    exact hx27
  let x29 : ℝ := -(97 / 500)
  have hx29 : Bounds (-97 / 500) (-97 / 500) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 500) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (403 / 500) (403 / 500) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(97 / 500)
  have hx31 : Bounds (403 / 500) (403 / 500) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-215671537 / 1000000000) (-13479471 / 62500000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_6117.1) (by simpa only [div_one] using reflection_log_6117.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-86915629411 / 500000000000) (-5432226813 / 31250000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (18937851947 / 500000000000) (18937852947 / 500000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (18937851947 / 1000000000000) (18937852947 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (18937851947 / 1000000000000) (18937852947 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18937852947 / 1000000000000) (-18937851947 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (674209327053 / 1000000000000) (674209329053 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (674209327053 / 1000000000000) (674209329053 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (97 / 500)
  have hx41 : Bounds (674209327053 / 1000000000000) (674209329053 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674189672511 / 1000000000000) (674209329053 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1941 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1941 / 10000000)
  have hx45 : Bounds (10001941 / 10000000) (10001941 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1941 / 10000000)
  have hx46 : Bounds (10001941 / 10000000) (10001941 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (194081 / 1000000000) (97041 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_6132.1) (by simpa only [div_one] using reflection_log_6132.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (194118671 / 1000000000000) (24264959 / 125000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1941 / 10000000)
  have hx49 : Bounds (-1941 / 10000000) (-1941 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998059 / 10000000) (9998059 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1941 / 10000000)
  have hx51 : Bounds (9998059 / 10000000) (9998059 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1941 / 10000000)
  have hx52 : Bounds (-1941 / 10000000) (-1941 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998059 / 10000000) (9998059 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1941 / 10000000)
  have hx54 : Bounds (9998059 / 10000000) (9998059 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-194119 / 1000000000) (-97059 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6133.1) (by simpa only [div_one] using reflection_log_6133.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-97040661 / 500000000000) (-194080321 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (37349 / 1000000000000) (39351 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (9337 / 500000000000) (4919 / 250000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (9337 / 500000000000) (4919 / 250000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-4919 / 250000000000) (-9337 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (173286790081 / 250000000000) (346573581163 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (173286790081 / 250000000000) (346573581163 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1941 / 10000000)
  have hx64 : Bounds (173286790081 / 250000000000) (346573581163 / 500000000000) x64 := by
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
  have hx86 : Bounds (173286790081 / 250000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (273467366567 / 200000000000) (1367356510053 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (683668416417 / 1000000000000) (683678255027 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (683668416417 / 1000000000000) (683678255027 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (10293673353951 / 1000000000000) (644974871779 / 62500000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7037459361009 / 1000000000000) (7055284717987 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7037459361009 / 1000000000000) (7055284717987 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(97569 / 1000000)
  have hx95 : Bounds (1097569 / 1000000) (1097569 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97569 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(97569 / 1000000)
  have hx96 : Bounds (1097569 / 1000000) (1097569 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97569 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (46548867 / 500000000) (18619547 / 200000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_6134.1) (by simpa only [div_one] using reflection_log_6134.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (12772648351 / 125000000000) (102181187907 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(97569 / 1000000)
  have hx99 : Bounds (-97569 / 1000000) (-97569 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97569 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (902431 / 1000000) (902431 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(97569 / 1000000)
  have hx101 : Bounds (902431 / 1000000) (902431 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(97569 / 1000000)
  have hx102 : Bounds (-97569 / 1000000) (-97569 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97569 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (902431 / 1000000) (902431 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(97569 / 1000000)
  have hx104 : Bounds (902431 / 1000000) (902431 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-51331523 / 500000000) (-20532609 / 200000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_6135.1) (by simpa only [div_one] using reflection_log_6135.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-18529263053 / 200000000000) (-46323157181 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (9534871543 / 1000000000000) (1906974709 / 200000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4767435771 / 1000000000000) (4767436773 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4767435771 / 1000000000000) (4767436773 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4767436773 / 1000000000000) (-4767435771 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688379743227 / 1000000000000) (688379745229 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688379743227 / 1000000000000) (688379745229 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (97569 / 1000000)
  have hx114 : Bounds (688379743227 / 1000000000000) (688379745229 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(48907 / 500000)
  have hx116 : Bounds (548907 / 500000) (548907 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48907 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(48907 / 500000)
  have hx117 : Bounds (548907 / 500000) (548907 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48907 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (93320929 / 1000000000) (9332093 / 100000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_6136.1) (by simpa only [div_one] using reflection_log_6136.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (102449022349 / 1000000000000) (12806127931 / 125000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(48907 / 500000)
  have hx120 : Bounds (-48907 / 500000) (-48907 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48907 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (451093 / 500000) (451093 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(48907 / 500000)
  have hx122 : Bounds (451093 / 500000) (451093 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(48907 / 500000)
  have hx123 : Bounds (-48907 / 500000) (-48907 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48907 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (451093 / 500000) (451093 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(48907 / 500000)
  have hx125 : Bounds (451093 / 500000) (451093 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-25733643 / 250000000) (-102934571 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_6137.1) (by simpa only [div_one] using reflection_log_6137.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-3714645191 / 40000000000) (-11608266109 / 125000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4791446287 / 500000000000) (598930911 / 62500000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4791446287 / 1000000000000) (598930911 / 125000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4791446287 / 1000000000000) (598930911 / 125000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-598930911 / 125000000000) (-4791446287 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (86044466589 / 125000000000) (688355734713 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (86044466589 / 125000000000) (688355734713 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (48907 / 500000)
  have hx135 : Bounds (86044466589 / 125000000000) (688355734713 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(97569 / 1000000)
  have hx136 : Bounds (343318936197 / 500000000000) (13767541493 / 20000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((97569 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(48907 / 500000)
  have hx137 : Bounds (688362049937 / 1000000000000) (345052809703 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((48907 / 500000) : ℝ)) <;> norm_num
  have hc : Bounds (97569 / 1000000) (48907 / 500000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(97569 / 1000000) ≤ (13767541493 / 20000000000) := hx136.2
      have h2 : (688379743227 / 1000000000000) ≤ biasE (97569 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (48907 / 500000) ≤ (688355734713 / 1000000000000) := hx135.2
      have h2 : (688362049937 / 1000000000000) ≤ x93*(48907 / 500000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(48907 / 500000)
  have hx139 : Bounds (548907 / 500000) (548907 / 500000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48907 / 500000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(48907 / 500000)
  have hx140 : Bounds (548907 / 500000) (548907 / 500000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48907 / 500000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (93320929 / 1000000000) (9332093 / 100000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_6136.1) (by simpa only [div_one] using reflection_log_6136.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (102449022349 / 1000000000000) (12806127931 / 125000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(48907 / 500000)
  have hx143 : Bounds (-48907 / 500000) (-48907 / 500000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48907 / 500000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (451093 / 500000) (451093 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(48907 / 500000)
  have hx145 : Bounds (451093 / 500000) (451093 / 500000) x145 := by
    exact hx144
  let x146 : ℝ := -(48907 / 500000)
  have hx146 : Bounds (-48907 / 500000) (-48907 / 500000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48907 / 500000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (451093 / 500000) (451093 / 500000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(48907 / 500000)
  have hx148 : Bounds (451093 / 500000) (451093 / 500000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-25733643 / 250000000) (-102934571 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_6137.1) (by simpa only [div_one] using reflection_log_6137.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-3714645191 / 40000000000) (-11608266109 / 125000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (4791446287 / 500000000000) (598930911 / 62500000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4791446287 / 1000000000000) (598930911 / 125000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4791446287 / 1000000000000) (598930911 / 125000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-598930911 / 125000000000) (-4791446287 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (86044466589 / 125000000000) (688355734713 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (86044466589 / 125000000000) (688355734713 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (48907 / 500000)
  have hx158 : Bounds (86044466589 / 125000000000) (688355734713 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(97569 / 1000000)
  have hx160 : Bounds (1097569 / 1000000) (1097569 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97569 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(97569 / 1000000)
  have hx161 : Bounds (1097569 / 1000000) (1097569 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97569 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (46548867 / 500000000) (18619547 / 200000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_6134.1) (by simpa only [div_one] using reflection_log_6134.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (12772648351 / 125000000000) (102181187907 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(97569 / 1000000)
  have hx164 : Bounds (-97569 / 1000000) (-97569 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97569 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (902431 / 1000000) (902431 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(97569 / 1000000)
  have hx166 : Bounds (902431 / 1000000) (902431 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(97569 / 1000000)
  have hx167 : Bounds (-97569 / 1000000) (-97569 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97569 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (902431 / 1000000) (902431 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(97569 / 1000000)
  have hx169 : Bounds (902431 / 1000000) (902431 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-51331523 / 500000000) (-20532609 / 200000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_6135.1) (by simpa only [div_one] using reflection_log_6135.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-18529263053 / 200000000000) (-46323157181 / 500000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (9534871543 / 1000000000000) (1906974709 / 200000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4767435771 / 1000000000000) (4767436773 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4767435771 / 1000000000000) (4767436773 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4767436773 / 1000000000000) (-4767435771 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688379743227 / 1000000000000) (688379745229 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688379743227 / 1000000000000) (688379745229 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (97569 / 1000000)
  have hx179 : Bounds (688379743227 / 1000000000000) (688379745229 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (86044466589 / 125000000000) (688379745229 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-2391894649 / 250000000000) (-9519709761 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4806821 / 500000000) (-9565311 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_6138.1) (by simpa only [div_one] using reflection_log_6139.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4806821 / 1000000000) (-9565311 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4806821 / 1000000000) (-9565311 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (9565311 / 2000000000) (4806821 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1395859671 / 2000000000) (348977001 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1395859671 / 2000000000) (348977001 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (97569 / 1000000) (48907 / 500000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-2391894649 / 250000000000) (-9519709761 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1097569 / 1000000) (548907 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-48907 / 500000) (-97569 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (451093 / 500000) (902431 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (451093 / 500000) (902431 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1108117961373 / 1000000000000) (554209442399 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (608117961373 / 500000000000) (304209442399 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (608117961373 / 500000000000) (304209442399 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (9788039 / 50000000) (98127751 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_6140.1) (by simpa only [div_one] using reflection_log_6141.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (9788039 / 100000000) (98127751 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (9788039 / 100000000) (98127751 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (597 / 500) (11941 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1941 / 10000) (-97 / 500) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8059 / 10000) (403 / 500) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8059 / 10000) (403 / 500) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1240694789081 / 1000000000000) (1240848740539 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (740694789081 / 500000000000) (740848740539 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (740694789081 / 500000000000) (740848740539 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (392980551 / 1000000000) (196594189 / 500000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_6142.1) (by simpa only [div_one] using reflection_log_6143.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (392980551 / 2000000000) (196594189 / 1000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (392980551 / 2000000000) (196594189 / 1000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1395859671 / 1000000000) (348977001 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (97569 / 1000000) (48907 / 500000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-2391894649 / 250000000000) (-9519709761 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (346573023101 / 250000000000) (1386388294239 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (346573023101 / 250000000000) (1386388294239 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (954262109019 / 1000000000000) (954361620777 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (683668416417 / 500000000000) (683678255027 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (122619547671 / 125000000000) (122631400669 / 125000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (122619547671 / 125000000000) (122631400669 / 125000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (41915555989 / 31250000000) (268289350467 / 200000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1395859671 / 2000000000) (348977001 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (487106055281 / 1000000000000) (121784947227 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339965849033 / 1000000000000) (170000582601 / 500000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339965849033 / 1000000000000) (170000582601 / 500000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (455995442543 / 1000000000000) (456093458851 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (438506617709 / 200000000000) (438600874791 / 200000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (130765703073 / 62500000000) (2092919208699 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (130765703073 / 62500000000) (2092919208699 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-98127751 / 1000000000) (-9788039 / 100000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1395859671 / 1000000000) (348977001 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (97569 / 1000000) (48907 / 500000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-2391894649 / 250000000000) (-9519709761 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (346573023101 / 250000000000) (1386388294239 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (346573023101 / 250000000000) (1386388294239 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-136043165327 / 1000000000000) (-67845405329 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1009611205649 / 1000000000000) (1009660001419 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (98506755723 / 1000000000000) (98758883379 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (98506755723 / 1000000000000) (98758883379 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (98506755723 / 500000000000) (98758883379 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (97569 / 500000) (48907 / 250000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-48907 / 250000) (-97569 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (692755723 / 500000000000) (1189883379 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (692755723 / 500000000000) (1189883379 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (476862373 / 500000000000) (327636647 / 200000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-135089440581 / 1000000000000) (-134052627423 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (683668416417 / 500000000000) (683678255027 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (122619547671 / 125000000000) (122631400669 / 125000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (122619547671 / 125000000000) (122631400669 / 125000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (41915555989 / 31250000000) (268289350467 / 200000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1395859671 / 2000000000) (348977001 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (487106055281 / 1000000000000) (121784947227 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339965849033 / 1000000000000) (170000582601 / 500000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339965849033 / 1000000000000) (170000582601 / 500000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (455995442543 / 1000000000000) (456093458851 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (438506617709 / 200000000000) (438600874791 / 200000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-29625173407 / 100000000000) (-293914821231 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-29625173407 / 100000000000) (-293914821231 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (97569 / 250000) (48907 / 125000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1009611205649 / 1000000000000) (1009660001419 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (78805404579 / 200000000000) (98758883379 / 250000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (78805404579 / 200000000000) (98758883379 / 250000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (292707 / 1000000) (146721 / 500000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (43203271059 / 62500000000) (27652387299 / 40000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (72326485897 / 50000000000) (28932994409 / 20000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (423409374149 / 1000000000000) (424507787269 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (423409374149 / 1000000000000) (424507787269 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-424507787269 / 1000000000000) (-423409374149 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-15240382187 / 500000000000) (-28373840633 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-15240382187 / 500000000000) (-28373840633 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-12758755451 / 200000000000) (-14841300877 / 250000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-14401820453 / 40000000000) (-353280024739 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1395859671 / 1000000000) (348977001 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (97569 / 1000000) (48907 / 500000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (9519709761 / 1000000000000) (2391894649 / 250000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-2391894649 / 250000000000) (-9519709761 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (346573023101 / 250000000000) (1386388294239 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (346573023101 / 250000000000) (1386388294239 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (135259133163 / 1000000000000) (135608184613 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (247608105351 / 250000000000) (990480290239 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (122619547671 / 125000000000) (122631400669 / 125000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (122619547671 / 125000000000) (122631400669 / 125000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1395859671 / 2000000000) (348977001 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (487106055281 / 1000000000000) (121784947227 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (487106055281 / 1000000000000) (121784947227 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (47782979333 / 100000000000) (119477269271 / 250000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2092448224883 / 1000000000000) (2092795413679 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (141511366543 / 500000000000) (4434377919 / 15625000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (141511366543 / 500000000000) (4434377919 / 15625000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (1917135969 / 100000000000) (19229664003 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (353763546201 / 500000000000) (44225588077 / 62500000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (353763546201 / 500000000000) (44225588077 / 62500000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (250297293241 / 500000000000) (250355538017 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (250297293241 / 500000000000) (250355538017 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-180278775397 / 1000000000000) (-22106258487 / 125000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (130765703073 / 31250000000) (2092919208699 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (1917135969 / 100000000000) (19229664003 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (353763546201 / 500000000000) (44225588077 / 62500000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (740162221449 / 250000000000) (740484662419 / 250000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-98127751 / 1000000000) (-9788039 / 100000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (196725049 / 2000000000) (98713799 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (196725049 / 2000000000) (98713799 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (58243379713 / 200000000000) (58476843303 / 200000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (3466816349 / 31250000000) (115534148619 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (97 / 500) (1941 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (9409 / 250000) (3767481 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (9409 / 250000) (3767481 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3767481 / 100000000) (-9409 / 250000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96232519 / 100000000) (240591 / 250000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96232519 / 100000000) (240591 / 250000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1014753773 / 976562500) (1039149770153 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1014753773 / 976562500) (1039149770153 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1014753773 / 976562500) (1039149770153 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (294091147513 / 1000000000000) (2949108989 / 10000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (405029270681 / 1000000000000) (410445047519 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (86044466589 / 125000000000) (688379745229 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (473833614757 / 1000000000000) (236933336821 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (473833614757 / 1000000000000) (236933336821 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (191916483409 / 1000000000000) (194496229381 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (238576292703 / 500000000000) (477175974177 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (419132585929 / 200000000000) (1047882826779 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (100548064967 / 250000000000) (101904629321 / 250000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (100548064967 / 250000000000) (101904629321 / 250000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (11961150547486215148201 / 28942014640500000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_440 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((97 / 500):ℝ) ((1941 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (11961150547486215148201 / 28942014640500000000000) := by
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
  have hsl : (96903 / 1000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1942941 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1941 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_440 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_440 {a z : ℝ}
    (ha : a ∈ Set.Icc ((97 / 500):ℝ) ((1941 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_440 ha ⟨hz.1.le,hz.2⟩ hs) (M := (11961150547486215148201 / 28942014640500000000000))
  exact lt_of_lt_of_le (by norm_num : (11961150547486215148201 / 28942014640500000000000) < 2*((97 / 500):ℝ)/(1-((97 / 500):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0441 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_441 (a z s c : ℝ)
    (ha : Bounds (1941 / 10000) (971 / 5000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1939059 / 20000000) (971971 / 10000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (3829467743093259506074172947 / 9260697713085361000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(971 / 5000)
  have hx1 : Bounds (5971 / 5000) (5971 / 5000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((971 / 5000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(971 / 5000)
  have hx2 : Bounds (5971 / 5000) (5971 / 5000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((971 / 5000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (35495301 / 200000000) (88738253 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6144.1) (by simpa only [div_one] using reflection_log_6144.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (211942442271 / 1000000000000) (105971221733 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(971 / 5000)
  have hx5 : Bounds (-971 / 5000) (-971 / 5000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((971 / 5000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (4029 / 5000) (4029 / 5000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(971 / 5000)
  have hx7 : Bounds (4029 / 5000) (4029 / 5000) x7 := by
    exact hx6
  let x8 : ℝ := -(971 / 5000)
  have hx8 : Bounds (-971 / 5000) (-971 / 5000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((971 / 5000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (4029 / 5000) (4029 / 5000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(971 / 5000)
  have hx10 : Bounds (4029 / 5000) (4029 / 5000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-215919707 / 1000000000) (-107959853 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_6145.1) (by simpa only [div_one] using reflection_log_6145.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-173988099901 / 1000000000000) (-86994049547 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (3795434237 / 100000000000) (9488586093 / 250000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (3795434237 / 200000000000) (9488586093 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (3795434237 / 200000000000) (9488586093 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-9488586093 / 500000000000) (-3795434237 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (337085003907 / 500000000000) (134834001963 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (337085003907 / 500000000000) (134834001963 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (971 / 5000)
  have hx20 : Bounds (337085003907 / 500000000000) (134834001963 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1941 / 10000)
  have hx22 : Bounds (11941 / 10000) (11941 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1941 / 10000)
  have hx23 : Bounds (11941 / 10000) (11941 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1941 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (177392763 / 1000000000) (44348191 / 250000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6130.1) (by simpa only [div_one] using reflection_log_6130.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (105912349149 / 500000000000) (211824699493 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1941 / 10000)
  have hx26 : Bounds (-1941 / 10000) (-1941 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8059 / 10000) (8059 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1941 / 10000)
  have hx28 : Bounds (8059 / 10000) (8059 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1941 / 10000)
  have hx29 : Bounds (-1941 / 10000) (-1941 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1941 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8059 / 10000) (8059 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1941 / 10000)
  have hx31 : Bounds (8059 / 10000) (8059 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-107897807 / 500000000) (-215795613 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_6131.1) (by simpa only [div_one] using reflection_log_6131.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-173909685323 / 1000000000000) (-43477421129 / 250000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (1516600519 / 40000000000) (37915014977 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (18957506487 / 1000000000000) (18957507489 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (18957506487 / 1000000000000) (18957507489 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18957507489 / 1000000000000) (-18957506487 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (674189672511 / 1000000000000) (674189674513 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (674189672511 / 1000000000000) (674189674513 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1941 / 10000)
  have hx41 : Bounds (674189672511 / 1000000000000) (674189674513 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (337085003907 / 500000000000) (674189674513 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (971 / 5000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(971 / 5000000)
  have hx45 : Bounds (5000971 / 5000000) (5000971 / 5000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((971 / 5000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(971 / 5000000)
  have hx46 : Bounds (5000971 / 5000000) (5000971 / 5000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((971 / 5000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (194181 / 1000000000) (97091 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_6146.1) (by simpa only [div_one] using reflection_log_6146.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (194218709 / 1000000000000) (194219711 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(971 / 5000000)
  have hx49 : Bounds (-971 / 5000000) (-971 / 5000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((971 / 5000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (4999029 / 5000000) (4999029 / 5000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(971 / 5000000)
  have hx51 : Bounds (4999029 / 5000000) (4999029 / 5000000) x51 := by
    exact hx50
  let x52 : ℝ := -(971 / 5000000)
  have hx52 : Bounds (-971 / 5000000) (-971 / 5000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((971 / 5000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (4999029 / 5000000) (4999029 / 5000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(971 / 5000000)
  have hx54 : Bounds (4999029 / 5000000) (4999029 / 5000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-194219 / 1000000000) (-97109 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6147.1) (by simpa only [div_one] using reflection_log_6147.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-194181283 / 1000000000000) (-97090141 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (18713 / 500000000000) (39429 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (18713 / 1000000000000) (3943 / 200000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (18713 / 1000000000000) (3943 / 200000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-3943 / 200000000000) (-18713 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (138629432057 / 200000000000) (693147162287 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (138629432057 / 200000000000) (693147162287 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (971 / 5000000)
  have hx64 : Bounds (138629432057 / 200000000000) (693147162287 / 1000000000000) x64 := by
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
  have hx86 : Bounds (138629432057 / 200000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1367317168099 / 1000000000000) (1367336855513 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (683658584049 / 1000000000000) (683668427757 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (683658584049 / 1000000000000) (683668427757 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (5144186400623 / 500000000000) (2062856261723 / 200000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (1758433595367 / 250000000000) (1410309697141 / 200000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (1758433595367 / 250000000000) (1410309697141 / 200000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(4881 / 50000)
  have hx95 : Bounds (54881 / 50000) (54881 / 50000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4881 / 50000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(4881 / 50000)
  have hx96 : Bounds (54881 / 50000) (54881 / 50000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4881 / 50000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (93144199 / 1000000000) (465721 / 5000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_6148.1) (by simpa only [div_one] using reflection_log_6148.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (51118467853 / 500000000000) (25559234201 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(4881 / 50000)
  have hx99 : Bounds (-4881 / 50000) (-4881 / 50000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4881 / 50000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (45119 / 50000) (45119 / 50000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(4881 / 50000)
  have hx101 : Bounds (45119 / 50000) (45119 / 50000) x101 := by
    exact hx100
  let x102 : ℝ := -(4881 / 50000)
  have hx102 : Bounds (-4881 / 50000) (-4881 / 50000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4881 / 50000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (45119 / 50000) (45119 / 50000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(4881 / 50000)
  have hx104 : Bounds (45119 / 50000) (45119 / 50000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-51359781 / 500000000) (-102719561 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_6149.1) (by simpa only [div_one] using reflection_log_6149.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-46346039179 / 500000000000) (-18538415491 / 200000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (2386214337 / 250000000000) (9544859349 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (2386214337 / 500000000000) (190897187 / 40000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (2386214337 / 500000000000) (190897187 / 40000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-190897187 / 40000000000) (-2386214337 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (27534990013 / 40000000000) (344187376163 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (27534990013 / 40000000000) (344187376163 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (4881 / 50000)
  have hx114 : Bounds (27534990013 / 40000000000) (344187376163 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(19573 / 200000)
  have hx116 : Bounds (219573 / 200000) (219573 / 200000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19573 / 200000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(19573 / 200000)
  have hx117 : Bounds (219573 / 200000) (219573 / 200000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19573 / 200000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (11670923 / 125000000) (18673477 / 200000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_6150.1) (by simpa only [div_one] using reflection_log_6150.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (20500956607 / 200000000000) (51252392067 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(19573 / 200000)
  have hx120 : Bounds (-19573 / 200000) (-19573 / 200000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19573 / 200000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (180427 / 200000) (180427 / 200000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(19573 / 200000)
  have hx122 : Bounds (180427 / 200000) (180427 / 200000) x122 := by
    exact hx121
  let x123 : ℝ := -(19573 / 200000)
  have hx123 : Bounds (-19573 / 200000) (-19573 / 200000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19573 / 200000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (180427 / 200000) (180427 / 200000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(19573 / 200000)
  have hx125 : Bounds (180427 / 200000) (180427 / 200000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-102991103 / 1000000000) (-51495551 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_6151.1) (by simpa only [div_one] using reflection_log_6151.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-18582375741 / 200000000000) (-46455938901 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (959290433 / 100000000000) (2398226583 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (959290433 / 200000000000) (2398226583 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (959290433 / 200000000000) (2398226583 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2398226583 / 500000000000) (-959290433 / 200000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (344175363417 / 500000000000) (137670145767 / 200000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (344175363417 / 500000000000) (137670145767 / 200000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (19573 / 200000)
  have hx135 : Bounds (344175363417 / 500000000000) (137670145767 / 200000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(4881 / 50000)
  have hx136 : Bounds (343316575159 / 500000000000) (27534886527 / 40000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((4881 / 50000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(19573 / 200000)
  have hx137 : Bounds (344178207621 / 500000000000) (345049896277 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((19573 / 200000) : ℝ)) <;> norm_num
  have hc : Bounds (4881 / 50000) (19573 / 200000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(4881 / 50000) ≤ (27534886527 / 40000000000) := hx136.2
      have h2 : (27534990013 / 40000000000) ≤ biasE (4881 / 50000) := hx114.1
      linarith
    · have h1 : biasE (19573 / 200000) ≤ (137670145767 / 200000000000) := hx135.2
      have h2 : (344178207621 / 500000000000) ≤ x93*(19573 / 200000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(19573 / 200000)
  have hx139 : Bounds (219573 / 200000) (219573 / 200000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19573 / 200000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(19573 / 200000)
  have hx140 : Bounds (219573 / 200000) (219573 / 200000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19573 / 200000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (11670923 / 125000000) (18673477 / 200000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_6150.1) (by simpa only [div_one] using reflection_log_6150.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (20500956607 / 200000000000) (51252392067 / 500000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(19573 / 200000)
  have hx143 : Bounds (-19573 / 200000) (-19573 / 200000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19573 / 200000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (180427 / 200000) (180427 / 200000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(19573 / 200000)
  have hx145 : Bounds (180427 / 200000) (180427 / 200000) x145 := by
    exact hx144
  let x146 : ℝ := -(19573 / 200000)
  have hx146 : Bounds (-19573 / 200000) (-19573 / 200000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19573 / 200000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (180427 / 200000) (180427 / 200000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(19573 / 200000)
  have hx148 : Bounds (180427 / 200000) (180427 / 200000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-102991103 / 1000000000) (-51495551 / 500000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_6151.1) (by simpa only [div_one] using reflection_log_6151.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-18582375741 / 200000000000) (-46455938901 / 500000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (959290433 / 100000000000) (2398226583 / 250000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (959290433 / 200000000000) (2398226583 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (959290433 / 200000000000) (2398226583 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-2398226583 / 500000000000) (-959290433 / 200000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (344175363417 / 500000000000) (137670145767 / 200000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (344175363417 / 500000000000) (137670145767 / 200000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (19573 / 200000)
  have hx158 : Bounds (344175363417 / 500000000000) (137670145767 / 200000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(4881 / 50000)
  have hx160 : Bounds (54881 / 50000) (54881 / 50000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4881 / 50000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(4881 / 50000)
  have hx161 : Bounds (54881 / 50000) (54881 / 50000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4881 / 50000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (93144199 / 1000000000) (465721 / 5000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_6148.1) (by simpa only [div_one] using reflection_log_6148.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (51118467853 / 500000000000) (25559234201 / 250000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(4881 / 50000)
  have hx164 : Bounds (-4881 / 50000) (-4881 / 50000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4881 / 50000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (45119 / 50000) (45119 / 50000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(4881 / 50000)
  have hx166 : Bounds (45119 / 50000) (45119 / 50000) x166 := by
    exact hx165
  let x167 : ℝ := -(4881 / 50000)
  have hx167 : Bounds (-4881 / 50000) (-4881 / 50000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4881 / 50000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (45119 / 50000) (45119 / 50000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(4881 / 50000)
  have hx169 : Bounds (45119 / 50000) (45119 / 50000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-51359781 / 500000000) (-102719561 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_6149.1) (by simpa only [div_one] using reflection_log_6149.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-46346039179 / 500000000000) (-18538415491 / 200000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (2386214337 / 250000000000) (9544859349 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (2386214337 / 500000000000) (190897187 / 40000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (2386214337 / 500000000000) (190897187 / 40000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-190897187 / 40000000000) (-2386214337 / 500000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (27534990013 / 40000000000) (344187376163 / 500000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (27534990013 / 40000000000) (344187376163 / 500000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (4881 / 50000)
  have hx179 : Bounds (27534990013 / 40000000000) (344187376163 / 500000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (344175363417 / 500000000000) (344187376163 / 500000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-383102329 / 40000000000) (-23824161 / 2500000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-9623719 / 1000000000) (-4787681 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_6152.1) (by simpa only [div_one] using reflection_log_6153.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-9623719 / 2000000000) (-4787681 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-9623719 / 2000000000) (-4787681 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (4787681 / 1000000000) (9623719 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (697934861 / 1000000000) (1395918081 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (697934861 / 1000000000) (1395918081 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (4881 / 50000) (19573 / 200000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-383102329 / 40000000000) (-23824161 / 2500000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (54881 / 50000) (219573 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-19573 / 200000) (-4881 / 50000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (180427 / 200000) (45119 / 50000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (180427 / 200000) (45119 / 50000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (277045147277 / 250000000000) (554240773277 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (152045147277 / 125000000000) (304240773277 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (152045147277 / 125000000000) (304240773277 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (195863761 / 1000000000) (24544811 / 125000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_6154.1) (by simpa only [div_one] using reflection_log_6155.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (195863761 / 2000000000) (24544811 / 250000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (195863761 / 2000000000) (24544811 / 250000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11941 / 10000) (5971 / 5000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-971 / 5000) (-1941 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (4029 / 5000) (8059 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (4029 / 5000) (8059 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (620424370269 / 500000000000) (1241002730207 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (370424370269 / 250000000000) (741002730207 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (370424370269 / 250000000000) (741002730207 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (393188377 / 1000000000) (98349053 / 250000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_6156.1) (by simpa only [div_one] using reflection_log_6157.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (393188377 / 2000000000) (98349053 / 500000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (393188377 / 2000000000) (98349053 / 500000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (697934861 / 500000000) (1395918081 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (4881 / 50000) (19573 / 200000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-383102329 / 40000000000) (-23824161 / 2500000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (55451686551 / 40000000000) (6931942083 / 5000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (55451686551 / 40000000000) (6931942083 / 5000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477127609269 / 500000000000) (190870956581 / 200000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (683658584049 / 500000000000) (683668427757 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (980936613171 / 1000000000000) (122628935713 / 125000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (980936613171 / 1000000000000) (122628935713 / 125000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (335312868001 / 250000000000) (1341400506823 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (697934861 / 1000000000) (1395918081 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (487113070199 / 1000000000000) (60893352777 / 125000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (16998659647 / 50000000000) (340008528617 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (16998659647 / 50000000000) (340008528617 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (890604581 / 1953125000) (456087612611 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1096280596479 / 500000000000) (2193032734917 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (261532870043 / 125000000000) (523232819909 / 250000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (261532870043 / 125000000000) (523232819909 / 250000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-24544811 / 250000000) (-195863761 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (697934861 / 500000000) (1395918081 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (4881 / 50000) (19573 / 200000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-383102329 / 40000000000) (-23824161 / 2500000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (55451686551 / 40000000000) (6931942083 / 5000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (55451686551 / 40000000000) (6931942083 / 5000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-136114566633 / 1000000000000) (-3394054963 / 25000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1009621352661 / 1000000000000) (1009670174889 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (49279618223 / 500000000000) (49405685833 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (49279618223 / 500000000000) (49405685833 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (49279618223 / 250000000000) (49405685833 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (4881 / 25000) (19573 / 100000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-19573 / 100000) (-4881 / 25000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (347118223 / 250000000000) (595685833 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (347118223 / 250000000000) (595685833 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (238939081 / 250000000000) (25628443 / 15625000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-135158810309 / 1000000000000) (-16765247271 / 125000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (683658584049 / 500000000000) (683668427757 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (980936613171 / 1000000000000) (122628935713 / 125000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (980936613171 / 1000000000000) (122628935713 / 125000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (335312868001 / 250000000000) (1341400506823 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (697934861 / 1000000000) (1395918081 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (487113070199 / 1000000000000) (60893352777 / 125000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (16998659647 / 50000000000) (340008528617 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (16998659647 / 50000000000) (340008528617 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (890604581 / 1953125000) (456087612611 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1096280596479 / 500000000000) (2193032734917 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-296407695421 / 1000000000000) (-294070644453 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-296407695421 / 1000000000000) (-294070644453 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (4881 / 12500) (19573 / 50000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1009621352661 / 1000000000000) (1009670174889 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (394236945787 / 1000000000000) (395245486663 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (394236945787 / 1000000000000) (395245486663 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (14643 / 50000) (58719 / 200000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691250349231 / 1000000000000) (17282693127 / 25000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1446533813699 / 1000000000000) (723326940169 / 500000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (423631892679 / 1000000000000) (212365172999 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (423631892679 / 1000000000000) (212365172999 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-212365172999 / 500000000000) (-423631892679 / 1000000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-30493400211 / 1000000000000) (-221768797 / 7812500000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-30493400211 / 1000000000000) (-221768797 / 7812500000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-510564729 / 8000000000) (-14847956471 / 250000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-180114143273 / 500000000000) (-353462470337 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (697934861 / 500000000) (1395918081 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (4881 / 50000) (19573 / 200000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (23824161 / 2500000000) (383102329 / 40000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-383102329 / 40000000000) (-23824161 / 2500000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (55451686551 / 40000000000) (6931942083 / 5000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (55451686551 / 40000000000) (6931942083 / 5000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (135329841027 / 1000000000000) (135678902391 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (39616897671 / 40000000000) (2476175839 / 2500000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (980936613171 / 1000000000000) (122628935713 / 125000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (980936613171 / 1000000000000) (122628935713 / 125000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (697934861 / 1000000000) (1395918081 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (487113070199 / 1000000000000) (60893352777 / 125000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (487113070199 / 1000000000000) (60893352777 / 125000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (7466047583 / 15625000000) (95581274151 / 200000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2092460074177 / 1000000000000) (2092807449497 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (283172289193 / 1000000000000) (4436715901 / 15625000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (283172289193 / 1000000000000) (4436715901 / 15625000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (19191524681 / 1000000000000) (1203116259 / 62500000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (141508450303 / 200000000000) (70762461247 / 100000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (141508450303 / 200000000000) (70762461247 / 100000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (250308018839 / 500000000000) (250366296087 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (250308018839 / 500000000000) (250366296087 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-180378043697 / 1000000000000) (-176948981367 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (261532870043 / 62500000000) (523232819909 / 125000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (19191524681 / 1000000000000) (1203116259 / 62500000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (141508450303 / 200000000000) (70762461247 / 100000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1480364445723 / 500000000000) (1481009685679 / 500000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-24544811 / 250000000) (-195863761 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (196829889 / 2000000000) (197532451 / 2000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (196829889 / 2000000000) (197532451 / 2000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (291379969531 / 1000000000000) (292547473167 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (55500962917 / 500000000000) (577992459 / 5000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1941 / 10000) (971 / 5000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3767481 / 100000000) (942841 / 25000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3767481 / 100000000) (942841 / 25000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-942841 / 25000000) (-3767481 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (24057159 / 25000000) (96232519 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (24057159 / 25000000) (96232519 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (129893721269 / 125000000000) (1039191701731 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (129893721269 / 125000000000) (1039191701731 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (129893721269 / 125000000000) (1039191701731 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (73564604807 / 250000000000) (11803131769 / 40000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (202630172531 / 500000000000) (16427071441 / 40000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (344175363417 / 500000000000) (344187376163 / 500000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (118456680783 / 250000000000) (11846494991 / 25000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (118456680783 / 250000000000) (11846494991 / 25000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (48005795329 / 250000000000) (194603219543 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477149158829 / 1000000000000) (238586279929 / 500000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2095677924769 / 1000000000000) (2095780703993 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (402418742127 / 1000000000000) (203922836227 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (402418742127 / 1000000000000) (203922836227 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (3829467743093259506074172947 / 9260697713085361000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_441 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1941 / 10000):ℝ) ((971 / 5000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (3829467743093259506074172947 / 9260697713085361000000000000) := by
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
  have hsl : (1939059 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (971971 / 10000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (971 / 5000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_441 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_441 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1941 / 10000):ℝ) ((971 / 5000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_441 ha ⟨hz.1.le,hz.2⟩ hs) (M := (3829467743093259506074172947 / 9260697713085361000000000000))
  exact lt_of_lt_of_le (by norm_num : (3829467743093259506074172947 / 9260697713085361000000000000) < 2*((1941 / 10000):ℝ)/(1-((1941 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0442 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_442 (a z s c : ℝ)
    (ha : Bounds (971 / 5000) (1943 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (970029 / 10000000) (1944943 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (478920903069862218382097159 / 1157493798302562000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1943 / 10000)
  have hx1 : Bounds (11943 / 10000) (11943 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1943 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1943 / 10000)
  have hx2 : Bounds (11943 / 10000) (11943 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1943 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (177560239 / 1000000000) (2219503 / 12500000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6158.1) (by simpa only [div_one] using reflection_log_6158.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (212060193437 / 1000000000000) (26507524329 / 125000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1943 / 10000)
  have hx5 : Bounds (-1943 / 10000) (-1943 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1943 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8057 / 10000) (8057 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1943 / 10000)
  have hx7 : Bounds (8057 / 10000) (8057 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1943 / 10000)
  have hx8 : Bounds (-1943 / 10000) (-1943 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1943 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8057 / 10000) (8057 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1943 / 10000)
  have hx10 : Bounds (8057 / 10000) (8057 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-43208763 / 200000000) (-108021907 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_6159.1) (by simpa only [div_one] using reflection_log_6159.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-87033250873 / 500000000000) (-174066500939 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (37993691691 / 1000000000000) (37993693693 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (3799369169 / 200000000000) (18996846847 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (3799369169 / 200000000000) (18996846847 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18996846847 / 1000000000000) (-3799369169 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674150333153 / 1000000000000) (134830067031 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674150333153 / 1000000000000) (134830067031 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1943 / 10000)
  have hx20 : Bounds (674150333153 / 1000000000000) (134830067031 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(971 / 5000)
  have hx22 : Bounds (5971 / 5000) (5971 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((971 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(971 / 5000)
  have hx23 : Bounds (5971 / 5000) (5971 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((971 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (35495301 / 200000000) (88738253 / 500000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6144.1) (by simpa only [div_one] using reflection_log_6144.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (211942442271 / 1000000000000) (105971221733 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(971 / 5000)
  have hx26 : Bounds (-971 / 5000) (-971 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((971 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4029 / 5000) (4029 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(971 / 5000)
  have hx28 : Bounds (4029 / 5000) (4029 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(971 / 5000)
  have hx29 : Bounds (-971 / 5000) (-971 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((971 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4029 / 5000) (4029 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(971 / 5000)
  have hx31 : Bounds (4029 / 5000) (4029 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-215919707 / 1000000000) (-107959853 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_6145.1) (by simpa only [div_one] using reflection_log_6145.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-173988099901 / 1000000000000) (-86994049547 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (3795434237 / 100000000000) (9488586093 / 250000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (3795434237 / 200000000000) (9488586093 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (3795434237 / 200000000000) (9488586093 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-9488586093 / 500000000000) (-3795434237 / 200000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (337085003907 / 500000000000) (134834001963 / 200000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (337085003907 / 500000000000) (134834001963 / 200000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (971 / 5000)
  have hx41 : Bounds (337085003907 / 500000000000) (134834001963 / 200000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674150333153 / 1000000000000) (134834001963 / 200000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1943 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1943 / 10000000)
  have hx45 : Bounds (10001943 / 10000000) (10001943 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1943 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1943 / 10000000)
  have hx46 : Bounds (10001943 / 10000000) (10001943 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1943 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (194281 / 1000000000) (97141 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_6160.1) (by simpa only [div_one] using reflection_log_6160.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (48579687 / 250000000000) (194319749 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1943 / 10000000)
  have hx49 : Bounds (-1943 / 10000000) (-1943 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1943 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998057 / 10000000) (9998057 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1943 / 10000000)
  have hx51 : Bounds (9998057 / 10000000) (9998057 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1943 / 10000000)
  have hx52 : Bounds (-1943 / 10000000) (-1943 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1943 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998057 / 10000000) (9998057 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1943 / 10000000)
  have hx54 : Bounds (9998057 / 10000000) (9998057 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-194319 / 1000000000) (-97159 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6161.1) (by simpa only [div_one] using reflection_log_6161.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-48570311 / 250000000000) (-48570061 / 250000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (293 / 7812500000) (7901 / 200000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (293 / 15625000000) (19753 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (293 / 15625000000) (19753 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-19753 / 1000000000000) (-293 / 15625000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147160247 / 1000000000000) (86643395281 / 125000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147160247 / 1000000000000) (86643395281 / 125000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1943 / 10000000)
  have hx64 : Bounds (693147160247 / 1000000000000) (86643395281 / 125000000000) x64 := by
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
  have hx86 : Bounds (693147160247 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (6836487467 / 5000000000) (273463438163 / 200000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (6836487467 / 10000000000) (42728662213 / 62500000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (6836487467 / 10000000000) (42728662213 / 62500000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (1028307770459 / 100000000000) (161077658503 / 15625000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7030013184961 / 1000000000000) (3523908024441 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7030013184961 / 1000000000000) (3523908024441 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(97671 / 1000000)
  have hx95 : Bounds (1097671 / 1000000) (1097671 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97671 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(97671 / 1000000)
  have hx96 : Bounds (1097671 / 1000000) (1097671 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97671 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (46595331 / 500000000) (93190663 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_6162.1) (by simpa only [div_one] using reflection_log_6162.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (25573171787 / 250000000000) (51146344123 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(97671 / 1000000)
  have hx99 : Bounds (-97671 / 1000000) (-97671 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97671 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (902329 / 1000000) (902329 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(97671 / 1000000)
  have hx101 : Bounds (902329 / 1000000) (902329 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(97671 / 1000000)
  have hx102 : Bounds (-97671 / 1000000) (-97671 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97671 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (902329 / 1000000) (902329 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(97671 / 1000000)
  have hx104 : Bounds (902329 / 1000000) (902329 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-102776081 / 1000000000) (-1284701 / 12500000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_6163.1) (by simpa only [div_one] using reflection_log_6163.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-92737838393 / 1000000000000) (-9273783749 / 100000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (1910969751 / 200000000000) (2388712689 / 250000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4777424377 / 1000000000000) (2388712689 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4777424377 / 1000000000000) (2388712689 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2388712689 / 500000000000) (-4777424377 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (344184877311 / 500000000000) (688369756623 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (344184877311 / 500000000000) (688369756623 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (97671 / 1000000)
  have hx114 : Bounds (344184877311 / 500000000000) (688369756623 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(24479 / 250000)
  have hx116 : Bounds (274479 / 250000) (274479 / 250000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24479 / 250000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(24479 / 250000)
  have hx117 : Bounds (274479 / 250000) (274479 / 250000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24479 / 250000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (93413837 / 1000000000) (46706919 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_6164.1) (by simpa only [div_one] using reflection_log_6164.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (102560546263 / 1000000000000) (51280273681 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(24479 / 250000)
  have hx120 : Bounds (-24479 / 250000) (-24479 / 250000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24479 / 250000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (225521 / 250000) (225521 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(24479 / 250000)
  have hx122 : Bounds (225521 / 250000) (225521 / 250000) x122 := by
    exact hx121
  let x123 : ℝ := -(24479 / 250000)
  have hx123 : Bounds (-24479 / 250000) (-24479 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24479 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (225521 / 250000) (225521 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(24479 / 250000)
  have hx125 : Bounds (225521 / 250000) (225521 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-103047637 / 1000000000) (-25761909 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_6165.1) (by simpa only [div_one] using reflection_log_6165.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-363115721 / 3906250000) (-92957623673 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (9602921687 / 1000000000000) (9602923689 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4801460843 / 1000000000000) (960292369 / 200000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4801460843 / 1000000000000) (960292369 / 200000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-960292369 / 200000000000) (-4801460843 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (137669143631 / 200000000000) (688345720157 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (137669143631 / 200000000000) (688345720157 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (24479 / 250000)
  have hx135 : Bounds (137669143631 / 200000000000) (688345720157 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(97671 / 1000000)
  have hx136 : Bounds (171657104447 / 250000000000) (688367241311 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((97671 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(24479 / 250000)
  have hx137 : Bounds (344175385509 / 500000000000) (690093956243 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((24479 / 250000) : ℝ)) <;> norm_num
  have hc : Bounds (97671 / 1000000) (24479 / 250000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(97671 / 1000000) ≤ (688367241311 / 1000000000000) := hx136.2
      have h2 : (344184877311 / 500000000000) ≤ biasE (97671 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (24479 / 250000) ≤ (688345720157 / 1000000000000) := hx135.2
      have h2 : (344175385509 / 500000000000) ≤ x93*(24479 / 250000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(24479 / 250000)
  have hx139 : Bounds (274479 / 250000) (274479 / 250000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24479 / 250000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(24479 / 250000)
  have hx140 : Bounds (274479 / 250000) (274479 / 250000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((24479 / 250000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (93413837 / 1000000000) (46706919 / 500000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_6164.1) (by simpa only [div_one] using reflection_log_6164.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (102560546263 / 1000000000000) (51280273681 / 500000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(24479 / 250000)
  have hx143 : Bounds (-24479 / 250000) (-24479 / 250000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24479 / 250000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (225521 / 250000) (225521 / 250000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(24479 / 250000)
  have hx145 : Bounds (225521 / 250000) (225521 / 250000) x145 := by
    exact hx144
  let x146 : ℝ := -(24479 / 250000)
  have hx146 : Bounds (-24479 / 250000) (-24479 / 250000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((24479 / 250000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (225521 / 250000) (225521 / 250000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(24479 / 250000)
  have hx148 : Bounds (225521 / 250000) (225521 / 250000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-103047637 / 1000000000) (-25761909 / 250000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_6165.1) (by simpa only [div_one] using reflection_log_6165.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-363115721 / 3906250000) (-92957623673 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (9602921687 / 1000000000000) (9602923689 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4801460843 / 1000000000000) (960292369 / 200000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4801460843 / 1000000000000) (960292369 / 200000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-960292369 / 200000000000) (-4801460843 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (137669143631 / 200000000000) (688345720157 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (137669143631 / 200000000000) (688345720157 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (24479 / 250000)
  have hx158 : Bounds (137669143631 / 200000000000) (688345720157 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(97671 / 1000000)
  have hx160 : Bounds (1097671 / 1000000) (1097671 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97671 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(97671 / 1000000)
  have hx161 : Bounds (1097671 / 1000000) (1097671 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97671 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (46595331 / 500000000) (93190663 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_6162.1) (by simpa only [div_one] using reflection_log_6162.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (25573171787 / 250000000000) (51146344123 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(97671 / 1000000)
  have hx164 : Bounds (-97671 / 1000000) (-97671 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97671 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (902329 / 1000000) (902329 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(97671 / 1000000)
  have hx166 : Bounds (902329 / 1000000) (902329 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(97671 / 1000000)
  have hx167 : Bounds (-97671 / 1000000) (-97671 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97671 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (902329 / 1000000) (902329 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(97671 / 1000000)
  have hx169 : Bounds (902329 / 1000000) (902329 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-102776081 / 1000000000) (-1284701 / 12500000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_6163.1) (by simpa only [div_one] using reflection_log_6163.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-92737838393 / 1000000000000) (-9273783749 / 100000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (1910969751 / 200000000000) (2388712689 / 250000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4777424377 / 1000000000000) (2388712689 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4777424377 / 1000000000000) (2388712689 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-2388712689 / 500000000000) (-4777424377 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (344184877311 / 500000000000) (688369756623 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (344184877311 / 500000000000) (688369756623 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (97671 / 1000000)
  have hx179 : Bounds (344184877311 / 500000000000) (688369756623 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (137669143631 / 200000000000) (688369756623 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-599221441 / 62500000000) (-9539624241 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-48169 / 5000000) (-9585417 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_6166.1) (by simpa only [div_one] using reflection_log_6167.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-48169 / 10000000) (-9585417 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-48169 / 10000000) (-9585417 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (9585417 / 2000000000) (48169 / 10000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1395879777 / 2000000000) (697964081 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1395879777 / 2000000000) (697964081 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (97671 / 1000000) (24479 / 250000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-599221441 / 62500000000) (-9539624241 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1097671 / 1000000) (274479 / 250000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-24479 / 250000) (-97671 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (225521 / 250000) (902329 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (225521 / 250000) (902329 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1108243223923 / 1000000000000) (221708843079 / 200000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (608243223923 / 500000000000) (121708843079 / 100000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (608243223923 / 500000000000) (121708843079 / 100000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (97983371 / 500000000) (7858459 / 40000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_6168.1) (by simpa only [div_one] using reflection_log_6169.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (97983371 / 1000000000) (7858459 / 80000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (97983371 / 1000000000) (7858459 / 80000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (5971 / 5000) (11943 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1943 / 10000) (-971 / 5000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8057 / 10000) (4029 / 5000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8057 / 10000) (4029 / 5000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (620501365103 / 500000000000) (1241156758099 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (370501365103 / 250000000000) (741156758099 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (370501365103 / 250000000000) (741156758099 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (393396211 / 1000000000) (196802027 / 500000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_6170.1) (by simpa only [div_one] using reflection_log_6171.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (393396211 / 2000000000) (196802027 / 1000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (393396211 / 2000000000) (196802027 / 1000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1395879777 / 1000000000) (697964081 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (97671 / 1000000) (24479 / 250000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-599221441 / 62500000000) (-9539624241 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (173286529243 / 125000000000) (1386388537759 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (173286529243 / 125000000000) (1386388537759 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477124161673 / 500000000000) (954347940323 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (6836487467 / 5000000000) (42728662213 / 31250000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (980916834869 / 1000000000000) (981011755949 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (980916834869 / 1000000000000) (981011755949 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (26824102591 / 20000000000) (670677119151 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1395879777 / 2000000000) (697964081 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (487120087959 / 1000000000000) (487153858367 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (84995134969 / 250000000000) (340015895061 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (84995134969 / 250000000000) (340015895061 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (113995911007 / 250000000000) (456081761931 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2192589319437 / 1000000000000) (1096530558823 / 500000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2092274681859 / 1000000000000) (523235840157 / 250000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2092274681859 / 1000000000000) (523235840157 / 250000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-7858459 / 80000000) (-97983371 / 1000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1395879777 / 1000000000) (697964081 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (97671 / 1000000) (24479 / 250000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-599221441 / 62500000000) (-9539624241 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (173286529243 / 125000000000) (1386388537759 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (173286529243 / 125000000000) (1386388537759 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-68092984263 / 500000000000) (-4244799571 / 31250000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1009631505181 / 1000000000000) (504840176933 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (49305859371 / 500000000000) (9886386153 / 100000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (49305859371 / 500000000000) (9886386153 / 100000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (49305859371 / 250000000000) (9886386153 / 50000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (97671 / 500000) (24479 / 125000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-24479 / 125000) (-97671 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (347859371 / 250000000000) (119286153 / 50000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (347859371 / 250000000000) (119286153 / 50000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (478895017 / 500000000000) (1642259603 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-33807044623 / 250000000000) (-134191326669 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (6836487467 / 5000000000) (42728662213 / 31250000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (980916834869 / 1000000000000) (981011755949 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (980916834869 / 1000000000000) (981011755949 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (26824102591 / 20000000000) (670677119151 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1395879777 / 2000000000) (697964081 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (487120087959 / 1000000000000) (487153858367 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (84995134969 / 250000000000) (340015895061 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (84995134969 / 250000000000) (340015895061 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (113995911007 / 250000000000) (456081761931 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2192589319437 / 1000000000000) (1096530558823 / 500000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-296563660261 / 1000000000000) (-58845293923 / 200000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-296563660261 / 1000000000000) (-58845293923 / 200000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (97671 / 250000) (24479 / 62500) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1009631505181 / 1000000000000) (504840176933 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (39444687497 / 100000000000) (395455446117 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (39444687497 / 100000000000) (395455446117 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (293013 / 1000000) (73437 / 250000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (86406044971 / 125000000000) (345652882967 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (723268956573 / 500000000000) (1446658043913 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (52981801693 / 125000000000) (106238226771 / 250000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (52981801693 / 125000000000) (106238226771 / 250000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-106238226771 / 250000000000) (-52981801693 / 125000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-15253016057 / 500000000000) (-28398967427 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-15253016057 / 500000000000) (-28398967427 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-63847397373 / 1000000000000) (-29709220269 / 500000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-180205528817 / 500000000000) (-353644910153 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1395879777 / 1000000000) (697964081 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (97671 / 1000000) (24479 / 250000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (9539624241 / 1000000000000) (599221441 / 62500000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-599221441 / 62500000000) (-9539624241 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (173286529243 / 125000000000) (1386388537759 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (173286529243 / 125000000000) (1386388537759 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (135400548781 / 1000000000000) (4242175627 / 31250000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (61900778559 / 62500000000) (990460375759 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (980916834869 / 1000000000000) (981011755949 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (980916834869 / 1000000000000) (981011755949 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1395879777 / 2000000000) (697964081 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (487120087959 / 1000000000000) (487153858367 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (487120087959 / 1000000000000) (487153858367 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (477824294881 / 1000000000000) (238951831007 / 500000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2092471934167 / 1000000000000) (2092819496023 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (56664369639 / 200000000000) (35512431431 / 125000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (56664369639 / 200000000000) (35512431431 / 125000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (9605850331 / 500000000000) (4817516819 / 250000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (707557418817 / 1000000000000) (707639823899 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (707557418817 / 1000000000000) (707639823899 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (250318750461 / 500000000000) (31297132523 / 62500000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (250318750461 / 500000000000) (31297132523 / 62500000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-180477322137 / 1000000000000) (-5532747001 / 31250000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2092274681859 / 500000000000) (523235840157 / 125000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (9605850331 / 500000000000) (4817516819 / 250000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (707557418817 / 1000000000000) (707639823899 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (185050559169 / 62500000000) (2962100142291 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-7858459 / 80000000) (-97983371 / 1000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (12308421 / 125000000) (3088083 / 31250000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (12308421 / 125000000) (3088083 / 31250000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (72885766033 / 250000000000) (292710754999 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (22213148399 / 200000000000) (115662850967 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (971 / 5000) (1943 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (942841 / 25000000) (3775249 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (942841 / 25000000) (3775249 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3775249 / 100000000) (-942841 / 25000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96224751 / 100000000) (24057159 / 25000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96224751 / 100000000) (24057159 / 25000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (103919170173 / 100000000000) (1039233658293 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (103919170173 / 100000000000) (1039233658293 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (103919170173 / 100000000000) (1039233658293 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (294425713563 / 1000000000000) (36905714031 / 125000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (202745727779 / 500000000000) (82181712643 / 200000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (137669143631 / 200000000000) (688369756623 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (236909913851 / 500000000000) (236926460917 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (236909913851 / 500000000000) (236926460917 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (192129891607 / 1000000000000) (194710223287 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (119286432511 / 250000000000) (238584571631 / 500000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (523923232527 / 250000000000) (1047897882171 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (402645255503 / 1000000000000) (408072861239 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (402645255503 / 1000000000000) (408072861239 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (478920903069862218382097159 / 1157493798302562000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_442 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((971 / 5000):ℝ) ((1943 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (478920903069862218382097159 / 1157493798302562000000000000) := by
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
  have hsl : (970029 / 10000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1944943 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1943 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_442 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_442 {a z : ℝ}
    (ha : a ∈ Set.Icc ((971 / 5000):ℝ) ((1943 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_442 ha ⟨hz.1.le,hz.2⟩ hs) (M := (478920903069862218382097159 / 1157493798302562000000000000))
  exact lt_of_lt_of_le (by norm_num : (478920903069862218382097159 / 1157493798302562000000000000) < 2*((971 / 5000):ℝ)/(1-((971 / 5000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0443 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_443 (a z s c : ℝ)
    (ha : Bounds (1943 / 10000) (243 / 1250) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1941057 / 20000000) (243243 / 2500000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (1533306641195929727837220017 / 3703681082004800400000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(243 / 1250)
  have hx1 : Bounds (1493 / 1250) (1493 / 1250) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 1250) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(243 / 1250)
  have hx2 : Bounds (1493 / 1250) (1493 / 1250) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 1250) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (177643967 / 1000000000) (2775687 / 15625000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6172.1) (by simpa only [div_one] using reflection_log_6172.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (26522244273 / 125000000000) (10608897769 / 50000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(243 / 1250)
  have hx5 : Bounds (-243 / 1250) (-243 / 1250) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 1250) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1007 / 1250) (1007 / 1250) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(243 / 1250)
  have hx7 : Bounds (1007 / 1250) (1007 / 1250) x7 := by
    exact hx6
  let x8 : ℝ := -(243 / 1250)
  have hx8 : Bounds (-243 / 1250) (-243 / 1250) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 1250) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (1007 / 1250) (1007 / 1250) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(243 / 1250)
  have hx10 : Bounds (1007 / 1250) (1007 / 1250) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-108083969 / 500000000) (-216167937 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_6173.1) (by simpa only [div_one] using reflection_log_6173.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-174144890853 / 1000000000000) (-174144890047 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (38033063331 / 1000000000000) (38033065333 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (3803306333 / 200000000000) (19016532667 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (3803306333 / 200000000000) (19016532667 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-19016532667 / 1000000000000) (-3803306333 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (674130647333 / 1000000000000) (134826129867 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (674130647333 / 1000000000000) (134826129867 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (243 / 1250)
  have hx20 : Bounds (674130647333 / 1000000000000) (134826129867 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1943 / 10000)
  have hx22 : Bounds (11943 / 10000) (11943 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1943 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1943 / 10000)
  have hx23 : Bounds (11943 / 10000) (11943 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1943 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (177560239 / 1000000000) (2219503 / 12500000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6158.1) (by simpa only [div_one] using reflection_log_6158.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (212060193437 / 1000000000000) (26507524329 / 125000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1943 / 10000)
  have hx26 : Bounds (-1943 / 10000) (-1943 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1943 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8057 / 10000) (8057 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1943 / 10000)
  have hx28 : Bounds (8057 / 10000) (8057 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1943 / 10000)
  have hx29 : Bounds (-1943 / 10000) (-1943 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1943 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8057 / 10000) (8057 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1943 / 10000)
  have hx31 : Bounds (8057 / 10000) (8057 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-43208763 / 200000000) (-108021907 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_6159.1) (by simpa only [div_one] using reflection_log_6159.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-87033250873 / 500000000000) (-174066500939 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (37993691691 / 1000000000000) (37993693693 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (3799369169 / 200000000000) (18996846847 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (3799369169 / 200000000000) (18996846847 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18996846847 / 1000000000000) (-3799369169 / 200000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (674150333153 / 1000000000000) (134830067031 / 200000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (674150333153 / 1000000000000) (134830067031 / 200000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1943 / 10000)
  have hx41 : Bounds (674150333153 / 1000000000000) (134830067031 / 200000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (674130647333 / 1000000000000) (134830067031 / 200000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (243 / 1250000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(243 / 1250000)
  have hx45 : Bounds (1250243 / 1250000) (1250243 / 1250000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 1250000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(243 / 1250000)
  have hx46 : Bounds (1250243 / 1250000) (1250243 / 1250000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 1250000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (194381 / 1000000000) (97191 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_6174.1) (by simpa only [div_one] using reflection_log_6174.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (194418787 / 1000000000000) (48604947 / 250000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(243 / 1250000)
  have hx49 : Bounds (-243 / 1250000) (-243 / 1250000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 1250000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (1249757 / 1250000) (1249757 / 1250000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(243 / 1250000)
  have hx51 : Bounds (1249757 / 1250000) (1249757 / 1250000) x51 := by
    exact hx50
  let x52 : ℝ := -(243 / 1250000)
  have hx52 : Bounds (-243 / 1250000) (-243 / 1250000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 1250000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (1249757 / 1250000) (1249757 / 1250000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(243 / 1250000)
  have hx54 : Bounds (1249757 / 1250000) (1249757 / 1250000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-194419 / 1000000000) (-97209 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6175.1) (by simpa only [div_one] using reflection_log_6175.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-38876241 / 200000000000) (-38876041 / 200000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (18791 / 500000000000) (39583 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (18791 / 1000000000000) (1237 / 62500000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (18791 / 1000000000000) (1237 / 62500000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-1237 / 62500000000) (-18791 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (43321697513 / 62500000000) (693147162209 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (43321697513 / 62500000000) (693147162209 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (243 / 1250000)
  have hx64 : Bounds (43321697513 / 62500000000) (693147162209 / 1000000000000) x64 := by
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
  have hx86 : Bounds (43321697513 / 62500000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1367277807541 / 1000000000000) (273459503231 / 200000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (68363890377 / 100000000000) (341824379039 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (68363890377 / 100000000000) (341824379039 / 500000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (2055557611113 / 200000000000) (10303664446743 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (3513147879743 / 500000000000) (7044087402669 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (3513147879743 / 500000000000) (7044087402669 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(48861 / 500000)
  have hx95 : Bounds (548861 / 500000) (548861 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48861 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(48861 / 500000)
  have hx96 : Bounds (548861 / 500000) (548861 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48861 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (93237123 / 1000000000) (23309281 / 250000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_6176.1) (by simpa only [div_one] using reflection_log_6176.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (102348441133 / 1000000000000) (12793555279 / 125000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(48861 / 500000)
  have hx99 : Bounds (-48861 / 500000) (-48861 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48861 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (451139 / 500000) (451139 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(48861 / 500000)
  have hx101 : Bounds (451139 / 500000) (451139 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(48861 / 500000)
  have hx102 : Bounds (-48861 / 500000) (-48861 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48861 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (451139 / 500000) (451139 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(48861 / 500000)
  have hx104 : Bounds (451139 / 500000) (451139 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-102832603 / 1000000000) (-51416301 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_6177.1) (by simpa only [div_one] using reflection_log_6177.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-9278359537 / 100000000000) (-92783594467 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (9564845763 / 1000000000000) (1912969553 / 200000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4782422881 / 1000000000000) (4782423883 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4782422881 / 1000000000000) (4782423883 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-4782423883 / 1000000000000) (-4782422881 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (688364756117 / 1000000000000) (688364758119 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (688364756117 / 1000000000000) (688364758119 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (48861 / 500000)
  have hx114 : Bounds (688364756117 / 1000000000000) (688364758119 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(97967 / 1000000)
  have hx116 : Bounds (1097967 / 1000000) (1097967 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97967 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(97967 / 1000000)
  have hx117 : Bounds (1097967 / 1000000) (1097967 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97967 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (93460287 / 1000000000) (1460317 / 15625000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_6178.1) (by simpa only [div_one] using reflection_log_6178.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (12827038867 / 125000000000) (20523262407 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(97967 / 1000000)
  have hx120 : Bounds (-97967 / 1000000) (-97967 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97967 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (902033 / 1000000) (902033 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(97967 / 1000000)
  have hx122 : Bounds (902033 / 1000000) (902033 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(97967 / 1000000)
  have hx123 : Bounds (-97967 / 1000000) (-97967 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97967 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (902033 / 1000000) (902033 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(97967 / 1000000)
  have hx125 : Bounds (902033 / 1000000) (902033 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-4124167 / 40000000) (-51552087 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_6179.1) (by simpa only [div_one] using reflection_log_6179.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-2906355259 / 31250000000) (-18600673477 / 200000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (1201617831 / 125000000000) (192258893 / 20000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (1201617831 / 250000000000) (192258893 / 40000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (1201617831 / 250000000000) (192258893 / 40000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-192258893 / 40000000000) (-1201617831 / 250000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (27533628307 / 40000000000) (172085177419 / 250000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (27533628307 / 40000000000) (172085177419 / 250000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (97967 / 1000000)
  have hx135 : Bounds (27533628307 / 40000000000) (172085177419 / 250000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(48861 / 500000)
  have hx136 : Bounds (21456989819 / 31250000000) (172090577291 / 250000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((48861 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(97967 / 1000000)
  have hx137 : Bounds (688345116669 / 1000000000000) (345044055289 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((97967 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (48861 / 500000) (97967 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(48861 / 500000) ≤ (172090577291 / 250000000000) := hx136.2
      have h2 : (688364756117 / 1000000000000) ≤ biasE (48861 / 500000) := hx114.1
      linarith
    · have h1 : biasE (97967 / 1000000) ≤ (172085177419 / 250000000000) := hx135.2
      have h2 : (688345116669 / 1000000000000) ≤ x93*(97967 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(97967 / 1000000)
  have hx139 : Bounds (1097967 / 1000000) (1097967 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97967 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(97967 / 1000000)
  have hx140 : Bounds (1097967 / 1000000) (1097967 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97967 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (93460287 / 1000000000) (1460317 / 15625000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_6178.1) (by simpa only [div_one] using reflection_log_6178.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (12827038867 / 125000000000) (20523262407 / 200000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(97967 / 1000000)
  have hx143 : Bounds (-97967 / 1000000) (-97967 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97967 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (902033 / 1000000) (902033 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(97967 / 1000000)
  have hx145 : Bounds (902033 / 1000000) (902033 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(97967 / 1000000)
  have hx146 : Bounds (-97967 / 1000000) (-97967 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97967 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (902033 / 1000000) (902033 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(97967 / 1000000)
  have hx148 : Bounds (902033 / 1000000) (902033 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-4124167 / 40000000) (-51552087 / 500000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_6179.1) (by simpa only [div_one] using reflection_log_6179.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-2906355259 / 31250000000) (-18600673477 / 200000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (1201617831 / 125000000000) (192258893 / 20000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (1201617831 / 250000000000) (192258893 / 40000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (1201617831 / 250000000000) (192258893 / 40000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-192258893 / 40000000000) (-1201617831 / 250000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (27533628307 / 40000000000) (172085177419 / 250000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (27533628307 / 40000000000) (172085177419 / 250000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (97967 / 1000000)
  have hx158 : Bounds (27533628307 / 40000000000) (172085177419 / 250000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(48861 / 500000)
  have hx160 : Bounds (548861 / 500000) (548861 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48861 / 500000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(48861 / 500000)
  have hx161 : Bounds (548861 / 500000) (548861 / 500000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48861 / 500000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (93237123 / 1000000000) (23309281 / 250000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_6176.1) (by simpa only [div_one] using reflection_log_6176.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (102348441133 / 1000000000000) (12793555279 / 125000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(48861 / 500000)
  have hx164 : Bounds (-48861 / 500000) (-48861 / 500000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48861 / 500000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (451139 / 500000) (451139 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(48861 / 500000)
  have hx166 : Bounds (451139 / 500000) (451139 / 500000) x166 := by
    exact hx165
  let x167 : ℝ := -(48861 / 500000)
  have hx167 : Bounds (-48861 / 500000) (-48861 / 500000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48861 / 500000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (451139 / 500000) (451139 / 500000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(48861 / 500000)
  have hx169 : Bounds (451139 / 500000) (451139 / 500000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-102832603 / 1000000000) (-51416301 / 500000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_6177.1) (by simpa only [div_one] using reflection_log_6177.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-9278359537 / 100000000000) (-92783594467 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (9564845763 / 1000000000000) (1912969553 / 200000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4782422881 / 1000000000000) (4782423883 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4782422881 / 1000000000000) (4782423883 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-4782423883 / 1000000000000) (-4782422881 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (688364756117 / 1000000000000) (688364758119 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (688364756117 / 1000000000000) (688364758119 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (48861 / 500000)
  have hx179 : Bounds (688364756117 / 1000000000000) (688364758119 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (27533628307 / 40000000000) (688364758119 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-9597533089 / 1000000000000) (-2387397321 / 250000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-9643887 / 1000000000) (-4797739 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_6180.1) (by simpa only [div_one] using reflection_log_6181.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-9643887 / 2000000000) (-4797739 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-9643887 / 2000000000) (-4797739 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (4797739 / 1000000000) (9643887 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (697944919 / 1000000000) (1395938249 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (697944919 / 1000000000) (1395938249 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (48861 / 500000) (97967 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-9597533089 / 1000000000000) (-2387397321 / 250000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (548861 / 500000) (1097967 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-97967 / 1000000) (-48861 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (902033 / 1000000) (451139 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (902033 / 1000000) (451139 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1108305865819 / 1000000000000) (1108606891323 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (608305865819 / 500000000000) (608606891323 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (608305865819 / 500000000000) (608606891323 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (7842789 / 40000000) (196564463 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_6182.1) (by simpa only [div_one] using reflection_log_6183.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (7842789 / 80000000) (196564463 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (7842789 / 80000000) (196564463 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11943 / 10000) (1493 / 1250) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-243 / 1250) (-1943 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (1007 / 1250) (8057 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (1007 / 1250) (8057 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (620578379049 / 500000000000) (1241310824231 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (370578379049 / 250000000000) (741310824231 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (370578379049 / 250000000000) (741310824231 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (393604053 / 1000000000) (78762381 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_6184.1) (by simpa only [div_one] using reflection_log_6185.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (393604053 / 2000000000) (78762381 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (393604053 / 2000000000) (78762381 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (697944919 / 500000000) (1395938249 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (48861 / 500000) (97967 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-9597533089 / 1000000000000) (-2387397321 / 250000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386292304911 / 1000000000000) (346597164929 / 250000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386292304911 / 1000000000000) (346597164929 / 250000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477120713103 / 500000000000) (190868218881 / 200000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (68363890377 / 50000000000) (341824379039 / 250000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (980897046463 / 1000000000000) (122624002011 / 125000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (980897046463 / 1000000000000) (122624002011 / 125000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (134115876311 / 100000000000) (670653973483 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (697944919 / 1000000000) (1395938249 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (487127109957 / 1000000000000) (121790224689 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339987891301 / 1000000000000) (85005816499 / 250000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339987891301 / 1000000000000) (85005816499 / 250000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (455977739769 / 1000000000000) (228037954417 / 500000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2192617458257 / 1000000000000) (274136189331 / 125000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2092286410491 / 1000000000000) (1046477723769 / 500000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2092286410491 / 1000000000000) (1046477723769 / 500000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-196564463 / 2000000000) (-7842789 / 80000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (697944919 / 500000000) (1395938249 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (48861 / 500000) (97967 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-9597533089 / 1000000000000) (-2387397321 / 250000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386292304911 / 1000000000000) (346597164929 / 250000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386292304911 / 1000000000000) (346597164929 / 250000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-34064342801 / 250000000000) (-16988121937 / 125000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1009641663207 / 1000000000000) (63105658647 / 62500000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (98664202611 / 1000000000000) (98916352971 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (98664202611 / 1000000000000) (98916352971 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (98664202611 / 500000000000) (98916352971 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (48861 / 250000) (97967 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-97967 / 500000) (-48861 / 250000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (697202611 / 500000000000) (1194352971 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (697202611 / 500000000000) (1194352971 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (959825877 / 1000000000000) (411075247 / 250000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-135297545327 / 1000000000000) (-33565168627 / 250000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (68363890377 / 50000000000) (341824379039 / 250000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (980897046463 / 1000000000000) (122624002011 / 125000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (980897046463 / 1000000000000) (122624002011 / 125000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (134115876311 / 100000000000) (670653973483 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (697944919 / 1000000000) (1395938249 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (487127109957 / 1000000000000) (121790224689 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339987891301 / 1000000000000) (85005816499 / 250000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339987891301 / 1000000000000) (85005816499 / 250000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (455977739769 / 1000000000000) (228037954417 / 500000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2192617458257 / 1000000000000) (274136189331 / 125000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-59343925603 / 200000000000) (-294382298883 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-59343925603 / 200000000000) (-294382298883 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (48861 / 125000) (97967 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1009641663207 / 1000000000000) (63105658647 / 62500000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (394656810447 / 1000000000000) (395665411883 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (394656810447 / 1000000000000) (395665411883 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (146583 / 500000) (293901 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (138249273909 / 200000000000) (691303806029 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1446542014203 / 1000000000000) (1446662209103 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (84815387227 / 200000000000) (212587734959 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (84815387227 / 200000000000) (212587734959 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-212587734959 / 500000000000) (-84815387227 / 200000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-30518659471 / 1000000000000) (-7102881063 / 250000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-30518659471 / 1000000000000) (-7102881063 / 250000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-1996068581 / 31250000000) (-59445046093 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-360593822607 / 1000000000000) (-22114209061 / 62500000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (697944919 / 500000000) (1395938249 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (48861 / 500000) (97967 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (2387397321 / 250000000000) (9597533089 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-9597533089 / 1000000000000) (-2387397321 / 250000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386292304911 / 1000000000000) (346597164929 / 250000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386292304911 / 1000000000000) (346597164929 / 250000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (6773562831 / 50000000000) (135820337827 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (990402466911 / 1000000000000) (247612602679 / 250000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (980897046463 / 1000000000000) (122624002011 / 125000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (980897046463 / 1000000000000) (122624002011 / 125000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (697944919 / 1000000000) (1395938249 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (487127109957 / 1000000000000) (121790224689 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (487127109957 / 1000000000000) (121790224689 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (29863846463 / 62500000000) (47790095223 / 100000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2092483798857 / 1000000000000) (2092831547251 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (35433926211 / 125000000000) (284249087763 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (35433926211 / 125000000000) (284249087763 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (19231887633 / 1000000000000) (19290285449 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (176893148827 / 250000000000) (44228440223 / 62500000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (176893148827 / 250000000000) (44228440223 / 62500000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (50065897763 / 100000000000) (31298478793 / 62500000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (50065897763 / 100000000000) (31298478793 / 62500000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-180576609757 / 1000000000000) (-177146836793 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2092286410491 / 500000000000) (1046477723769 / 250000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (19231887633 / 1000000000000) (19290285449 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (176893148827 / 250000000000) (44228440223 / 62500000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2960889051197 / 1000000000000) (2962180956827 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-196564463 / 2000000000) (-7842789 / 80000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (19703959 / 200000000) (9887109 / 100000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (19703959 / 200000000) (9887109 / 100000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (291706182341 / 1000000000000) (292874059979 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (13891196573 / 125000000000) (57863611593 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1943 / 10000) (243 / 1250) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3775249 / 100000000) (59049 / 1562500) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3775249 / 100000000) (59049 / 1562500) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-59049 / 1562500) (-3775249 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (1503451 / 1562500) (96224751 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (1503451 / 1562500) (96224751 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (259808414573 / 250000000000) (207855127969 / 200000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (259808414573 / 250000000000) (207855127969 / 200000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (259808414573 / 250000000000) (207855127969 / 200000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (294593030111 / 1000000000000) (295413152561 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (81144520539 / 200000000000) (411140375747 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (27533628307 / 40000000000) (688364758119 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (236906464921 / 500000000000) (473846040221 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (236906464921 / 500000000000) (473846040221 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (96118307543 / 500000000000) (194817239023 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477142299317 / 1000000000000) (238582862571 / 500000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (419141588471 / 200000000000) (1047905416719 / 500000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (402871801047 / 1000000000000) (81660016017 / 200000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (402871801047 / 1000000000000) (81660016017 / 200000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (1533306641195929727837220017 / 3703681082004800400000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_443 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1943 / 10000):ℝ) ((243 / 1250)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (1533306641195929727837220017 / 3703681082004800400000000000) := by
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
  have hsl : (1941057 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (243243 / 2500000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (243 / 1250))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_443 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_443 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1943 / 10000):ℝ) ((243 / 1250)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_443 ha ⟨hz.1.le,hz.2⟩ hs) (M := (1533306641195929727837220017 / 3703681082004800400000000000))
  exact lt_of_lt_of_le (by norm_num : (1533306641195929727837220017 / 3703681082004800400000000000) < 2*((1943 / 10000):ℝ)/(1-((1943 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end


